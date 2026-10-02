use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{
    BasicBlock, Body, Location, NonDivergingIntrinsic, Place, ProjectionElem, START_BLOCK,
    StatementKind, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::print::with_no_trimmed_paths;

use crate::PassPolicy;

pub(super) struct RadWriteSets;

impl<'tcx> crate::MirPass<'tcx> for RadWriteSets {
    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(ctx.opts.unstable_opts.rad_write_sets)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if body.source.promoted.is_some() {
            return;
        }
        with_no_trimmed_paths!(print(tcx, body));
    }
}

/// The blocks that can run since the coroutine last started or resumed, up to a suspension.
struct Segment {
    blocks: DenseBitSet<BasicBlock>,
    from_entry: bool,
    /// Suspensions (by block) whose resumption starts this segment.
    after: DenseBitSet<BasicBlock>,
}

fn segment(body: &Body<'_>, end: BasicBlock) -> Segment {
    let n = body.basic_blocks.len();
    let mut segment = Segment {
        blocks: DenseBitSet::new_empty(n),
        from_entry: false,
        after: DenseBitSet::new_empty(n),
    };
    segment.blocks.insert(end);
    let mut stack = vec![end];
    while let Some(bb) = stack.pop() {
        segment.from_entry |= bb == START_BLOCK;
        for &pred in &body.basic_blocks.predecessors()[bb] {
            match body[pred].terminator().kind {
                // A suspension's drop edge leads to the coroutine being destroyed, not resumed.
                TerminatorKind::Yield { resume, .. } => {
                    if resume == bb {
                        segment.after.insert(pred);
                    }
                }
                _ => {
                    if segment.blocks.insert(pred) {
                        stack.push(pred);
                    }
                }
            }
        }
    }
    segment
}

fn print<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    // Find .await() calls where checkpoints get put
    let checkpoints: Vec<BasicBlock> = body
        .basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Yield { .. }))
        .map(|(bb, _)| bb)
        .collect();
    if checkpoints.is_empty() {
        return;
    }
    eprintln!("=== rad write sets: {} ===", tcx.def_path_str(body.source.def_id()));

    let suspension = |bb| checkpoints.iter().position(|&c| c == bb).unwrap();
    let source_map = tcx.sess.source_map();

    // Find segments between two await() calls
    for (index, &end) in checkpoints.iter().enumerate() {
        let segment = segment(body, end);
        let span = source_map.span_to_diagnostic_string(body[end].terminator().source_info.span);
        let starts = segment
            .from_entry
            .then(|| "entry".to_string())
            .into_iter()
            .chain(segment.after.iter().map(|bb| format!(".await {}", suspension(bb))));
        eprintln!(
            "  .await {index} ({end:?}) at {span}, since {}",
            starts.collect::<Vec<_>>().join(", ")
        );

        // Write returned by resume arg
        for bb in segment.after.iter() {
            let TerminatorKind::Yield { resume_arg, .. } = body[bb].terminator().kind else {
                unreachable!()
            };
            let location = body.terminator_loc(bb);
            eprintln!("    {location:?} resume {resume_arg:?}");
        }

        for bb in segment.blocks.iter() {
            let data = &body[bb];

            // Go through the rest of the block and find MIR statements that write to memory
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let label = match &statement.kind {
                    StatementKind::Assign(assign) => target(tcx, body, assign.0),
                    StatementKind::SetDiscriminant { place, .. } => target(tcx, body, **place),
                    StatementKind::Intrinsic(intrinsic)
                        if let NonDivergingIntrinsic::CopyNonOverlapping(..) = **intrinsic =>
                    {
                        "intrinsic"
                    }
                    _ => continue,
                };
                let location = Location { block: bb, statement_index };
                eprintln!("    {location:?} {label:<10} {statement:?}");
            }

            // await()'s return is checkpointed in the next segment
            if bb == end {
                continue;
            }

            // Look for Call, Drop, or InlineAsm
            let terminator = data.terminator();
            let label = match terminator.kind {
                TerminatorKind::Call { .. } | TerminatorKind::TailCall { .. } => "call",
                TerminatorKind::Drop { .. } => "drop",
                TerminatorKind::InlineAsm { .. } => "asm",
                _ => continue,
            };

            let mut head = String::new();
            terminator.kind.fmt_head(&mut head).unwrap();
            eprintln!("    {:?} {label:<10} {head}", body.terminator_loc(bb));
        }
    }
}

/// How an assignment reaches the memory it writes.
fn target<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: Place<'tcx>) -> &'static str {
    let Some((base, _)) = place.iter_projections().find(|(_, elem)| *elem == ProjectionElem::Deref)
    else {
        return "direct";
    };
    let ty = base.ty(body, tcx).ty;
    if ty.is_box() {
        "via Box"
    } else if ty.is_ref() {
        "via ref"
    } else {
        "via ptr"
    }
}
