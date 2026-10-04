use rustc_abi::FieldIdx;
use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_hir as hir;
use rustc_index::IndexVec;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    BasicBlock, Body, BodyLoans, CoroutineSavedLocal, InstructionLoans, LoanId, Local, Location,
    Mutability, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, START_BLOCK,
    Statement, StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{CAPTURE_STRUCT_LOCAL, TyCtxt, TypeVisitableExt};
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
        let Some(plan) = analyze(tcx, body) else { return };
        with_no_trimmed_paths!(print(tcx, body, &plan));
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

/// What the checkpoint at each `.await` of a body must save
struct CheckpointPlan<'tcx> {
    /// Polonius's results for the body
    loans: Option<&'tcx BodyLoans<'tcx>>,
    /// The list of items that need to be checkpointed
    suspensions: Vec<Suspension<'tcx>>,
}

/// One `.await`'s checkpoint
struct Suspension<'tcx> {
    /// The block where the `.await` has a `Yield`
    end: BasicBlock,
    /// The segment from the previous checkpoint to this one
    segment: Segment,
    /// The locals StateTransform stores in the future here
    saved: DenseBitSet<Local>,
    /// The writes the liveness filter kept
    writes: Vec<Write<'tcx>>,
    /// Number of writes to locals that were filtered out
    not_saved: usize,
    /// What the checkpoint must copy, and whether we should follow references
    objects: FxIndexMap<CheckpointObject, Depth>,
}

/// How much of an object the checkpoint copies
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Depth {
    /// Only the object's own bytes
    Shallow,
    /// The object and everything reachable through the references inside it
    Deep,
}

/// Something the checkpoint copies
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum CheckpointObject {
    /// The coroutine's state, which StateTransform writes at every suspension
    Discriminant,
    /// A local StateTransform stores in the future, as slot `_sN` of the coroutine layout
    Saved { slot: CoroutineSavedLocal, local: Local },
    /// A captured upvar (an argument of the async fn), or all of them if the field is unknown
    Upvar(Option<FieldIdx>),
    /// Memory outside the future, reached through a reference
    Outside,
}

/// Records that the checkpoint copies `object` at least `depth` deep
fn record(
    objects: &mut FxIndexMap<CheckpointObject, Depth>,
    object: CheckpointObject,
    depth: Depth,
) {
    let entry = objects.entry(object).or_insert(depth);
    *entry = (*entry).max(depth);
}

/// An instruction in a segment that writes memory the checkpoint may need
struct Write<'tcx> {
    location: Location,
    effect: Effect<'tcx>,
    /// The memory that the instruction can reach according to Polonius
    reach: Option<Reach<'tcx>>,
}

struct Reach<'tcx> {
    instruction: Option<&'tcx InstructionLoans>,
    targets: Targets<'tcx>,
}

/// Finds what the checkpoint at each `.await` must save
fn analyze<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<CheckpointPlan<'tcx>> {
    // Find .await() calls where checkpoints get put
    let checkpoints: Vec<BasicBlock> = body
        .basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Yield { .. }))
        .map(|(bb, _)| bb)
        .collect();
    if checkpoints.is_empty() {
        return None;
    }

    let movable = tcx.coroutine_movability(body.source.def_id()) == hir::Movability::Movable;
    let liveness =
        locals_live_across_suspend_points(tcx, body, &always_storage_live_locals(body), movable);

    // Get live aliasing info from polonius
    let def = body.source.def_id().expect_local();
    let loans = tcx
        .mir_borrowck(tcx.typeck_root_def_id_local(def))
        .ok()
        .and_then(|result| result.loans.get(&def));

    let analysis = Analysis {
        tcx,
        body,
        liveness,
        loans,
        // Find the poll loops to split checkpoint segments at
        poll_loops: poll_loops(body, &checkpoints),
        defs: LocalDefs::new(tcx, body),
    };

    // Find the items that need to be checkpointed
    let suspensions = checkpoints
        .iter()
        .enumerate()
        .map(|(index, &end)| analysis.suspension(index, end))
        .collect();

    Some(CheckpointPlan { loans, suspensions })
}

/// What `analyze` computes once per body, for every suspension to use
struct Analysis<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    liveness: LivenessInfo,
    loans: Option<&'tcx BodyLoans<'tcx>>,
    poll_loops: FxIndexMap<BasicBlock, PollLoop>,
    defs: LocalDefs,
}

impl<'tcx> Analysis<'_, 'tcx> {
    /// Finds what the checkpoint at the `index`th `.await`, whose `Yield` is `end`, must save
    fn suspension(&self, index: usize, end: BasicBlock) -> Suspension<'tcx> {
        let body = self.body;
        // Find segments between two await() calls
        let segment = segment(body, &self.poll_loops, end);

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

        let saved = saved_at(body, &self.liveness, index);
        let mut objects = FxIndexMap::default();
        // The state changes at every suspension
        record(&mut objects, CheckpointObject::Discriminant, Depth::Shallow);

        // Remove dead writes using liveness filter
        let mut writes = Vec::new();
        let mut not_saved = 0;
        for (location, effect) in effects.effects {
            // Find where it's actually writing
            if let Effect::Write(place, _) = effect
                && !place.is_indirect()
            {
                match self.object(place, &saved) {
                    Some(object) => record(&mut objects, object, Depth::Shallow),
                    // Drop writes to a temporary variable that aren't used after the checkpoint
                    None => {
                        not_saved += 1;
                        continue;
                    }
                }
            }
            // Find where this Place actually aliases
            let reach = if writes_through_pointers(&effect) {
                self.reach(location, &effect, &saved, &mut objects)
            } else {
                None
            };
            writes.push(Write { location, effect, reach });
        }
        Suspension { end, segment, saved, writes, not_saved, objects }
    }

    /// Find the saved local or upvar that holds `place` if it's stored in the future here
    fn object(&self, place: Place<'_>, saved: &DenseBitSet<Local>) -> Option<CheckpointObject> {
        if !in_future(place, saved) {
            return None;
        }
        if place.local == CAPTURE_STRUCT_LOCAL {
            let field = match place.projection.first() {
                Some(ProjectionElem::Field(field, _)) => Some(*field),
                _ => None,
            };
            return Some(CheckpointObject::Upvar(field));
        }
        let slot = self.liveness.saved_locals.get(place.local)?;
        Some(CheckpointObject::Saved { slot, local: place.local })
    }

    /// Figure out which objects an instruction can write through its pointers
    fn reach(
        &self,
        location: Location,
        effect: &Effect<'tcx>,
        saved: &DenseBitSet<Local>,
        objects: &mut FxIndexMap<CheckpointObject, Depth>,
    ) -> Option<Reach<'tcx>> {
        // Without borrowck's results, the pointers can hold any saved local or memory
        let Some(loans) = self.loans.filter(|_| !matches!(effect, Effect::Intrinsic)) else {
            for local in saved.iter() {
                if let Some(object) = self.object(local.into(), saved) {
                    record(objects, object, Depth::Shallow);
                }
            }
            record(objects, CheckpointObject::Outside, Depth::Shallow);
            return None;
        };

        let instruction = id_at(self.body, location).and_then(|id| loans.instructions.get(&id));
        let targets = targets(self.tcx, self.body, loans, instruction);
        // Pointer points to objects in the future, a shallow copy
        for &place in &targets.places {
            if let Some(object) = self.object(place, saved) {
                record(objects, object, Depth::Shallow);
            }
        }
        // Pointer points to memory outside the filter
        if targets.outside {
            match self.holders(location, effect, saved) {
                Some(holders) => {
                    for holder in holders {
                        if let Some(object) = self.object(holder.into(), saved) {
                            record(objects, object, Depth::Deep);
                        }
                    }
                }
                None => record(objects, CheckpointObject::Outside, Depth::Shallow),
            }
        }
        Some(Reach { instruction, targets })
    }

    /// Find all the references an instruction writes through
    fn holders(
        &self,
        location: Location,
        effect: &Effect<'tcx>,
        saved: &DenseBitSet<Local>,
    ) -> Option<Vec<Local>> {
        match *effect {
            // A write through a pointer
            Effect::Write(
                place,
                MutatingUseContext::Store | MutatingUseContext::SetDiscriminant,
            ) => Some(vec![self.pointer_holder(place, saved)?]),
            // A call can write through any reference among its arguments, or its destination's
            Effect::Call => {
                let TerminatorKind::Call { args, destination, .. } =
                    &self.body[location.block].terminator().kind
                else {
                    return None;
                };
                let mut holders = Vec::new();
                for arg in args {
                    // Only types with lifetimes hold references (regions are erased here)
                    if !arg.node.ty(self.body, self.tcx).has_erased_regions() {
                        continue;
                    }
                    match arg.node {
                        // A reference read out of memory may have changed since
                        Operand::Copy(place) | Operand::Move(place) if !place.is_indirect() => {
                            holders.push(self.holder(place.local, saved, 0)?);
                        }
                        _ => return None,
                    }
                }
                if destination.is_indirect() {
                    holders.push(self.pointer_holder(*destination, saved)?);
                }
                Some(holders)
            }
            // Drops and everything else
            _ => None,
        }
    }

    /// The saved local holding the reference that `place` writes through
    fn pointer_holder(&self, place: Place<'tcx>, saved: &DenseBitSet<Local>) -> Option<Local> {
        if !single_deref(place) {
            return None;
        }
        self.holder(place.local, saved, 0)
    }

    /// Follow the reference back to where it was originally stored
    fn holder(&self, local: Local, saved: &DenseBitSet<Local>, depth: usize) -> Option<Local> {
        // A saved local that can't change before the checkpoint still holds that reference then
        if saved.contains(local) && self.defs.fixed.contains(local) {
            return Some(local);
        }
        // Skip temporaries that are only assigned once
        if depth > 8 {
            return None;
        }
        let Def::Once(location) = self.defs.defs[local] else { return None };
        let statement = self.body.stmt_at(location).left()?;
        let StatementKind::Assign(assign) = &statement.kind else { return None };
        match &assign.1 {
            // A reborrow
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) if single_deref(*place) => {
                self.holder(place.local, saved, depth + 1)
            }
            // The same reference
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _) if !place.is_indirect() => {
                self.holder(place.local, saved, depth + 1)
            }
            _ => None,
        }
    }
}

/// Whether `place` is stored in the future at a checkpoint whose saved locals are `saved`
fn in_future(place: Place<'_>, saved: &DenseBitSet<Local>) -> bool {
    place.local == CAPTURE_STRUCT_LOCAL || saved.contains(place.local)
}

/// Whether an instruction can write memory through a pointer
fn writes_through_pointers(effect: &Effect<'_>) -> bool {
    match *effect {
        Effect::Write(place, context) => place.is_indirect() || context == MutatingUseContext::Drop,
        Effect::Call | Effect::Intrinsic => true,
    }
}

/// Whether `place` is `(*_n).projections` with no other dereference. A second dereference reads a
/// pointer out of memory, which may have changed by the checkpoint.
fn single_deref(place: Place<'_>) -> bool {
    place.projection.first() == Some(&ProjectionElem::Deref)
        && place.projection.iter().filter(|elem| *elem == ProjectionElem::Deref).count() == 1
}

/// Where each local's own bytes are written, and which locals keep their value
struct LocalDefs {
    defs: IndexVec<Local, Def>,
    /// Locals are fixed if assigned once, outside any loop, and never borrowed in a way that could change them
    fixed: DenseBitSet<Local>,
}

#[derive(Clone, Copy)]
enum Def {
    Never,
    /// Assigned as a whole by exactly one statement or call
    Once(Location),
    Many,
}

impl LocalDefs {
    fn new<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let mut visitor = LocalDefsVisitor {
            tcx,
            body,
            defs: IndexVec::from_elem(Def::Never, &body.local_decls),
            borrowed: DenseBitSet::new_empty(body.local_decls.len()),
        };
        visitor.visit_body(body);
        let LocalDefsVisitor { defs, borrowed, .. } = visitor;

        let mut fixed = DenseBitSet::new_empty(body.local_decls.len());
        for (local, def) in defs.iter_enumerated() {
            if let Def::Once(location) = *def
                && !borrowed.contains(local)
                && !on_cycle(body, location.block)
            {
                fixed.insert(local);
            }
        }
        LocalDefs { defs, fixed }
    }
}

struct LocalDefsVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    defs: IndexVec<Local, Def>,
    /// Mutably borrowed, or shared-borrowed with interior mutability
    borrowed: DenseBitSet<Local>,
}

impl<'tcx> Visitor<'tcx> for LocalDefsVisitor<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        // Uses through a pointer reach the pointee, not the local
        if place.is_indirect() {
            return;
        }
        let local = place.local;
        match context {
            PlaceContext::MutatingUse(
                MutatingUseContext::Borrow | MutatingUseContext::RawBorrow,
            ) => {
                self.borrowed.insert(local);
            }
            PlaceContext::NonMutatingUse(
                NonMutatingUseContext::SharedBorrow | NonMutatingUseContext::RawBorrow,
            ) => {
                let (tcx, body) = (self.tcx, self.body);
                if !place.ty(body, tcx).ty.is_freeze(tcx, body.typing_env(tcx)) {
                    self.borrowed.insert(local);
                }
            }
            PlaceContext::MutatingUse(MutatingUseContext::Store | MutatingUseContext::Call)
                if place.projection.is_empty() =>
            {
                self.defs[local] = match self.defs[local] {
                    Def::Never => Def::Once(location),
                    Def::Once(_) | Def::Many => Def::Many,
                };
            }
            // Writes to part of the local, drops, resume values, ...
            PlaceContext::MutatingUse(_) => self.defs[local] = Def::Many,
            _ => {}
        }
    }
}

/// Whether `block` is part of a loop
fn on_cycle(body: &Body<'_>, block: BasicBlock) -> bool {
    let mut seen = DenseBitSet::new_empty(body.basic_blocks.len());
    let mut stack: Vec<BasicBlock> = body[block].terminator().successors().collect();
    while let Some(bb) = stack.pop() {
        if bb == block {
            return true;
        }
        if seen.insert(bb) {
            stack.extend(body[bb].terminator().successors());
        }
    }
    false
}

fn print<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, plan: &CheckpointPlan<'tcx>) {
    eprintln!("=== rad write sets: {} ===", tcx.def_path_str(body.source.def_id()));
    let suspension = |bb| plan.suspensions.iter().position(|s| s.end == bb).unwrap();
    let source_map = tcx.sess.source_map();
    if plan.loans.is_none() {
        eprintln!("  polonius: no live loans recorded (needs `-Zpolonius=next`)");
    }

    // Find instructions with duplicated borrow checker IDs or no ID
    let unnumbered = unnumbered(body);
    let (shared, duplicated) = repeated_ids(body);
    eprintln!(
        "  ids: {} without one {unnumbered:?}, {shared} shared by elaborated drops, {duplicated} duplicated",
        unnumbered.len()
    );

    for (index, checkpoint) in plan.suspensions.iter().enumerate() {
        let (end, segment) = (checkpoint.end, &checkpoint.segment);
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
        let saved_list: Vec<String> =
            checkpoint.saved.iter().map(|local| format!("{local:?}")).collect();
        eprintln!("    saved: {}", saved_list.join(", "));

        for write in &checkpoint.writes {
            let location = write.location;
            match write.effect {
                Effect::Write(place, context) => {
                    let what = match context {
                        MutatingUseContext::Store => "store",
                        MutatingUseContext::SetDiscriminant => "discr",
                        MutatingUseContext::Call => "call dest",
                        MutatingUseContext::Yield => "resume",
                        MutatingUseContext::Drop => "drop",
                        MutatingUseContext::AsmOutput => "asm out",
                        _ => unreachable!("not recorded as a write: {context:?}"),
                    };
                    let how = access(tcx, body, place);
                    let id = id_label(body, location);
                    eprintln!("    {location:?} {id:<5} {what:<10} {how:<8} {place:?}");
                }
                Effect::Call => {
                    let mut head = String::new();
                    body[location.block].terminator().kind.fmt_head(&mut head).unwrap();
                    let id = id_label(body, location);
                    eprintln!("    {location:?} {id:<5} call       {head}");
                }
                Effect::Intrinsic => eprintln!("    {location:?} intrinsic  copy_nonoverlapping"),
            }
            if let (Some(reach), Some(loans)) = (&write.reach, plan.loans) {
                print_live_loans(loans, reach, &checkpoint.saved);
            }
        }
        eprintln!("    ({} writes to locals not saved here)", checkpoint.not_saved);
        let objects: Vec<String> = checkpoint
            .objects
            .iter()
            .map(|(object, depth)| {
                let object = match object {
                    CheckpointObject::Discriminant => "state".to_string(),
                    CheckpointObject::Saved { slot, local } => format!("{slot:?} ({local:?})"),
                    CheckpointObject::Upvar(Some(field)) => format!("upvar {field:?}"),
                    CheckpointObject::Upvar(None) => "upvars".to_string(),
                    CheckpointObject::Outside => "outside".to_string(),
                };
                match depth {
                    Depth::Shallow => object,
                    Depth::Deep => format!("{object} deep"),
                }
            })
            .collect();
        eprintln!("    checkpoint: {}", objects.join(", "));
    }
}

/// Prints which loans the pointers used by an instruction can hold, and the memory those loans
/// resolve to
fn print_live_loans<'tcx>(
    loans: &BodyLoans<'tcx>,
    reach: &Reach<'tcx>,
    saved: &DenseBitSet<Local>,
) {
    match reach.instruction {
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
    print_targets(&reach.targets, saved);
}

/// Prints the memory an instruction can write through its pointers, split by whether it is
/// saved in the future at this checkpoint
fn print_targets(targets: &Targets<'_>, saved: &DenseBitSet<Local>) {
    let kept: Vec<String> = targets
        .places
        .iter()
        .filter(|&&place| in_future(place, saved))
        .map(|place| format!("{place:?}"))
        .collect();
    let unsaved = targets.places.len() - kept.len();
    let outside = if targets.outside { " + outside" } else { "" };
    let fallback = if targets.fallback { " (fallback)" } else { "" };
    eprintln!(
        "                 targets: {{{}}}{outside}{fallback}, dropped {} unsaved, {} frozen",
        kept.join(", "),
        unsaved,
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

/// The locals at the `index`th checkpoint
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
fn access<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: Place<'tcx>) -> &'static str {
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
