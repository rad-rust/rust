use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_hir as hir;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    BasicBlock, Body, BodyLoans, InstructionLoans, LoanId, Local, Location, Mutability,
    NonDivergingIntrinsic, Place, ProjectionElem, START_BLOCK, Statement, StatementKind,
    Terminator, TerminatorKind,
};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{CAPTURE_STRUCT_LOCAL, TyCtxt};
use rustc_mir_dataflow::impls::always_storage_live_locals;

use crate::PassPolicy;
use crate::coroutine::layout::{LivenessInfo, locals_live_across_suspend_points};
use crate::rad_statement_ids::{id_at, id_label, repeated_ids, unnumbered};

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

/// The poll loop of an `.await`, which rustc lowers as
/// `loop { match poll(..) { Ready(r) => break r, Pending => {} } cx = yield () }`
struct PollLoop {
    /// The `Yield` that suspends while the awaited future is pending
    suspend: BasicBlock,
    /// The block the `Yield` resumes into, which jumps back to the loop head
    resume: BasicBlock,
}

/// Maps the head of each `.await`'s poll loop to that loop. A resume block that doesn't end in
/// a `goto` back to the head isn't recognised, so its `.await` keeps every path.
fn poll_loops(body: &Body<'_>, checkpoints: &[BasicBlock]) -> FxIndexMap<BasicBlock, PollLoop> {
    let mut loops = FxIndexMap::default();
    for &suspend in checkpoints {
        let TerminatorKind::Yield { resume, .. } = body[suspend].terminator().kind else {
            continue;
        };
        if let TerminatorKind::Goto { target: head } = body[resume].terminator().kind {
            loops.insert(head, PollLoop { suspend, resume });
        }
    }
    loops
}

fn segment(
    body: &Body<'_>,
    poll_loops: &FxIndexMap<BasicBlock, PollLoop>,
    end: BasicBlock,
) -> Segment {
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
            // Strangelove's API needs to guarantee that every await() returns `Pending` on its
            // first poll, so every `.await` suspends at least once. Leaving another `await()`'s
            // poll loop through `Ready` therefore means its `Yield` already ran and took a
            // checkpoint. So we need to remove the CFG edge that returns immediately in our analysis.
            if let Some(poll_loop) = poll_loops.get(&bb)
                && poll_loop.suspend != end
                && pred != poll_loop.resume
            {
                continue;
            }
            match body[pred].terminator().kind {
                // A suspension's drop edge leads to the coroutine being destroyed
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
    let movable = tcx.coroutine_movability(body.source.def_id()) == hir::Movability::Movable;
    let liveness =
        locals_live_across_suspend_points(tcx, body, &always_storage_live_locals(body), movable);
    let source_map = tcx.sess.source_map();

    // Get live aliasing info from polonius
    let def = body.source.def_id().expect_local();
    let loans = tcx
        .mir_borrowck(tcx.typeck_root_def_id_local(def))
        .ok()
        .and_then(|result| result.loans.get(&def));
    if loans.is_none() {
        eprintln!("  polonius: no live loans recorded (needs `-Zpolonius=next`)");
    }

    // Find instructions with duplicated borrow checker IDs or no ID
    let unnumbered = unnumbered(body);
    let (shared, duplicated) = repeated_ids(body);
    eprintln!(
        "  ids: {} without one {unnumbered:?}, {shared} shared by elaborated drops, {duplicated} duplicated",
        unnumbered.len()
    );

    // Find the poll loops to split checkpoint segments at
    let poll_loops = poll_loops(body, &checkpoints);

    for (index, &end) in checkpoints.iter().enumerate() {
        // Find segments between two await() calls
        let segment = segment(body, &poll_loops, end);
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
                    let id = id_label(body, location);
                    eprintln!("    {location:?} {id:<5} {what:<10} {how:<8} {place:?}");
                    // Find where this Place actually aliases
                    if place.is_indirect() || context == MutatingUseContext::Drop {
                        print_live_loans(tcx, loans, body, location, &saved);
                    }
                }
                Effect::Call => {
                    let mut head = String::new();
                    body[location.block].terminator().kind.fmt_head(&mut head).unwrap();
                    let id = id_label(body, location);
                    eprintln!("    {location:?} {id:<5} call       {head}");
                    print_live_loans(tcx, loans, body, location, &saved);
                }
                Effect::Intrinsic => eprintln!("    {location:?} intrinsic  copy_nonoverlapping"),
            }
        }
        eprintln!("    ({not_saved} writes to locals not saved here)");
    }
}

/// Prints which loans the pointers used by the instruction at `location` can hold, and the
/// memory those loans resolve to
fn print_live_loans<'tcx>(
    tcx: TyCtxt<'tcx>,
    loans: Option<&BodyLoans<'tcx>>,
    body: &Body<'tcx>,
    location: Location,
    saved: &DenseBitSet<Local>,
) {
    let Some(loans) = loans else { return };
    let instruction = id_at(body, location).and_then(|id| loans.instructions.get(&id));
    match instruction {
        Some(InstructionLoans { live, reachable: Some(reachable), outside }) => {
            let reachable: Vec<String> = reachable
                .iter()
                .filter_map(|loan| {
                    let (place, mutability) = loans.loans[loan]?;
                    Some(format!("{loan:?} &{}{place:?}", mutability.prefix_str()))
                })
                .collect();
            let outside = if *outside { " + outside" } else { "" };
            eprintln!(
                "                 reaches: {{{}}}{outside} (of {} live)",
                reachable.join(", "),
                live.count()
            );
        }
        _ => eprintln!("                 reaches: no borrowck result"),
    }
    print_targets(&targets(tcx, body, loans, instruction), saved);
}

/// Prints the memory an instruction can write through its pointers, split by whether it is
/// saved in the future at this checkpoint
fn print_targets(targets: &Targets<'_>, saved: &DenseBitSet<Local>) {
    let (kept, unsaved): (Vec<&Place<'_>>, Vec<_>) = targets
        .places
        .iter()
        .partition(|place| place.local == CAPTURE_STRUCT_LOCAL || saved.contains(place.local));
    let kept: Vec<String> = kept.iter().map(|place| format!("{place:?}")).collect();
    let outside = if targets.outside { " + outside" } else { "" };
    let fallback = if targets.fallback { " (fallback)" } else { "" };
    eprintln!(
        "                 targets: {{{}}}{outside}{fallback}, dropped {} unsaved, {} frozen",
        kept.join(", "),
        unsaved.len(),
        targets.frozen
    );
}

/// The memory a set of loans can point to
#[derive(Default)]
struct Targets<'tcx> {
    places: FxIndexSet<Place<'tcx>>,
    /// Memory this body didn't borrow
    outside: bool,
    /// The instruction had no borrowck result, so every loan still live was used instead
    fallback: bool,
    /// Skip shared loans of `Freeze` data
    frozen: usize,
}

/// Turns the loans an instruction's pointers can hold into the memory they point to
fn targets<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loans: &BodyLoans<'tcx>,
    instruction: Option<&InstructionLoans>,
) -> Targets<'tcx> {
    let mut targets = Targets::default();
    match instruction {
        Some(InstructionLoans { reachable: Some(reachable), outside, .. }) => {
            targets.outside = *outside;
            for loan in reachable.iter() {
                targets.add(tcx, body, loans, loan);
            }
        }
        // Without a result, the pointers can hold any loan still live here.
        Some(InstructionLoans { live, .. }) => {
            targets.fallback = true;
            targets.outside = true;
            for loan in live.iter() {
                targets.add(tcx, body, loans, loan);
            }
        }
        // If no result was found above, every loan in the body is marked
        None => {
            targets.fallback = true;
            targets.outside = true;
            for loan in loans.loans.indices() {
                targets.add(tcx, body, loans, loan);
            }
        }
    }
    targets
}

impl<'tcx> Targets<'tcx> {
    fn add(&mut self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>, loans: &BodyLoans<'tcx>, loan: LoanId) {
        // Fake borrows point to nothing
        let Some((place, mutability)) = loans.loans[loan] else { return };
        if mutability == Mutability::Not
            && place.ty(body, tcx).ty.is_freeze(tcx, body.typing_env(tcx))
        {
            self.frozen += 1;
            return;
        }
        match place.iter_projections().rev().find(|(_, elem)| *elem == ProjectionElem::Deref) {
            None => {
                self.places.insert(place);
            }
            // Reborrow's loans are a superset of the original's
            Some((base, _)) if base.ty(body, tcx).ty.is_ref() => {}
            // Polonius can't resolve where a Box aliases
            Some(_) => self.outside = true,
        }
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
