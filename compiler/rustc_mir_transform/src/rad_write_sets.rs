use rustc_hir as hir;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    BasicBlock, Body, Local, Location, NonDivergingIntrinsic, Place, ProjectionElem, START_BLOCK,
    Statement, StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{CAPTURE_STRUCT_LOCAL, TyCtxt};
use rustc_mir_dataflow::impls::always_storage_live_locals;

use crate::PassPolicy;
use crate::coroutine::layout::{LivenessInfo, locals_live_across_suspend_points};

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

/// The blocks in between two checkpoints
struct Segment {
    blocks: DenseBitSet<BasicBlock>,
    from_entry: bool,
    /// Set of earlier checkpoint Yield() that resume into this segment
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
    // The same computation `StateTransform` uses to choose what the future keeps at each
    // suspension, so a write kept here is a write to a field of the future.
    let movable = tcx.coroutine_movability(body.source.def_id()) == hir::Movability::Movable;
    let liveness =
        locals_live_across_suspend_points(tcx, body, &always_storage_live_locals(body), movable);
    let source_map = tcx.sess.source_map();

    for (index, &end) in checkpoints.iter().enumerate() {
        // Find segments between two await() calls
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
        let saved = saved_at(body, &liveness, index);
        let saved_list: Vec<String> = saved.iter().map(|local| format!("{local:?}")).collect();
        eprintln!("    saved: {}", saved_list.join(", "));

        // Find statements that modify objects
        let mut effects = Effects::default();
        for bb in segment.after.iter() {
            // Write returned by resume arg
            effects.visit_terminator(body[bb].terminator(), body.terminator_loc(bb));
        }
        for bb in segment.blocks.iter() {
            let data = &body[bb];
            for (statement_index, statement) in data.statements.iter().enumerate() {
                effects.visit_statement(statement, Location { block: bb, statement_index });
            }
            // await()'s return is checkpointed in the next segment
            if bb != end {
                effects.visit_terminator(data.terminator(), body.terminator_loc(bb));
            }
        }

        // Remove dead writes using liveness filter
        let mut not_saved = 0;
        for (location, effect) in effects.effects {
            match effect {
                Effect::Write(place, context) => {
                    // Drop writes to a temporary variable that aren't used after the checkpoint
                    if !place.is_indirect()
                        && place.local != CAPTURE_STRUCT_LOCAL
                        && !saved.contains(place.local)
                    {
                        not_saved += 1;
                        continue;
                    }
                    let what = match context {
                        MutatingUseContext::Store => "store",
                        MutatingUseContext::SetDiscriminant => "discr",
                        MutatingUseContext::Call => "call dest",
                        MutatingUseContext::Yield => "resume",
                        MutatingUseContext::Drop => "drop",
                        MutatingUseContext::AsmOutput => "asm out",
                        _ => unreachable!("not recorded as a write: {context:?}"),
                    };
                    let how = target(tcx, body, place);
                    eprintln!("    {location:?} {what:<10} {how:<8} {place:?}");
                }
                Effect::Call => {
                    let mut head = String::new();
                    body[location.block].terminator().kind.fmt_head(&mut head).unwrap();
                    eprintln!("    {location:?} call       {head}");
                }
                Effect::Intrinsic => eprintln!("    {location:?} intrinsic  copy_nonoverlapping"),
            }
        }
        eprintln!("    ({not_saved} writes to locals not saved here)");
    }
}

/// The locals `StateTransform` stores in the future at the `index`th suspension point.
fn saved_at(body: &Body<'_>, liveness: &LivenessInfo, index: usize) -> DenseBitSet<Local> {
    let mut saved = DenseBitSet::new_empty(body.local_decls.len());
    for (saved_local, local) in liveness.saved_locals.iter_enumerated() {
        if liveness.live_locals_at_suspension_points[index].contains(saved_local) {
            saved.insert(local);
        }
    }
    saved
}

/// What an instruction in a segment does to memory
enum Effect<'tcx> {
    /// Writes the place, directly or through a pointer
    Write(Place<'tcx>, MutatingUseContext),
    /// A call, which also writes whatever the callee reaches through its arguments
    Call,
    /// `copy_nonoverlapping`, which writes through a pointer
    Intrinsic,
}

#[derive(Default)]
struct Effects<'tcx> {
    effects: Vec<(Location, Effect<'tcx>)>,
}

impl<'tcx> Visitor<'tcx> for Effects<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        // Only match statements that change data
        if let PlaceContext::MutatingUse(
            context @ (MutatingUseContext::Store
            | MutatingUseContext::SetDiscriminant
            | MutatingUseContext::Call
            | MutatingUseContext::Yield
            | MutatingUseContext::Drop
            | MutatingUseContext::AsmOutput),
        ) = context
        {
            self.effects.push((location, Effect::Write(*place, context)));
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if let StatementKind::Intrinsic(intrinsic) = &statement.kind
            && let NonDivergingIntrinsic::CopyNonOverlapping(..) = **intrinsic
        {
            self.effects.push((location, Effect::Intrinsic));
        }
        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { .. } | TerminatorKind::TailCall { .. } = terminator.kind {
            self.effects.push((location, Effect::Call));
        }
        self.super_terminator(terminator, location);
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
