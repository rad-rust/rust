//! `-Zrad-write-sets`: prints every write each function may make, split into segments.
//!
//! A segment runs from the function's entry, or from resuming at a suspension point (a `Yield`,
//! i.e. an `.await`), to the next suspension point or the return. A plain function therefore has
//! a single segment, its complete write summary; a coroutine gets one segment per suspension
//! point plus one ending at its return.
//!
//! Nothing is filtered out. Every write is listed with what it lands in:
//!
//!   * a local, an argument or the return place of a plain function;
//!   * for coroutines, a field of the coroutine's state (a local saved across suspension points,
//!     reported as `_sN` like `CoroutineLayout`), whether that field is live at the suspension
//!     point ending the segment, or "not saved" for locals that don't survive a suspension;
//!   * memory reached through a reference, resolved to the local it points to where the
//!     reference's origin is known within the body;
//!   * otherwise, a write site whose address is only known at run time (the reference came from
//!     an argument, a captured variable, or was loaded from memory).
//!
//! The pass runs just before `StateTransform`: after drop elaboration, so drop flags are ordinary
//! locals, and before coroutine locals are moved into the coroutine's state.
//!
//! Calls are assumed to write only what is reachable from their arguments through writable
//! references (`&mut`, raw `*mut`, or `&` to a type with interior mutability), plus their
//! return value.

use std::borrow::Cow;
use std::cell::RefCell;
use std::hash::Hash;

use itertools::Itertools;
use rustc_data_structures::fx::{FxHashMap, FxIndexMap, FxIndexSet};
use rustc_hir as hir;
use rustc_index::IndexVec;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::*;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, CoroutineArgsExt, Ty, TyCtxt, TypingEnv};
use rustc_mir_dataflow::impls::always_storage_live_locals;
use rustc_session::Session;
use rustc_span::Symbol;
use rustc_span::source_map::Spanned;
use smallvec::SmallVec;

use crate::coroutine::{LivenessInfo, locals_live_across_suspend_points};

pub(super) struct RadWriteSets;

impl<'tcx> crate::MirPass<'tcx> for RadWriteSets {
    fn is_enabled(&self, sess: &Session) -> bool {
        // The standard library is built with `-Zforce-unstable-if-unmarked`; leave it out.
        sess.opts.unstable_opts.rad_write_sets
            && !sess.opts.unstable_opts.force_unstable_if_unmarked
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if body.source.promoted.is_some() || !tcx.def_kind(body.source.def_id()).is_fn_like() {
            return;
        }

        let segments = WriteSetAnalysis::new(tcx, body).run();
        let coroutine = body.coroutine_kind().map(|kind| {
            let always_live = always_storage_live_locals(body);
            let movable = kind.movability() == hir::Movability::Movable;
            locals_live_across_suspend_points(tcx, body, &always_live, movable)
        });

        with_no_trimmed_paths!(print_write_sets(tcx, body, &segments, coroutine.as_ref()));
    }

    fn is_required(&self) -> bool {
        true
    }
}

/// How a place gets written. `store` labels a store through a pointer `ThroughRef`, and
/// `record_targets` labels any write to unknown memory `WriteSite`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum WriteKind {
    /// An assignment or `SetDiscriminant` to the place.
    Store,
    /// The place is a call's destination.
    CallResult,
    /// A callee may write the place through a writable reference reachable from its arguments.
    CallArg,
    /// Dropped: drop glue takes `&mut place`.
    Drop,
    /// A store through a reference whose target is known.
    ThroughRef,
    /// A store through a reference (or a call argument) whose target is unknown here: the address
    /// is only known at run time.
    WriteSite,
    /// The resume argument, written when the coroutine resumes after a suspension point.
    Resume,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Write<'tcx> {
    place: Place<'tcx>,
    kind: WriteKind,
    /// The local holding the reference the write goes through, if any.
    via: Option<Local>,
}

/// What a pointer lets its holder do to the memory it points to. Ordered from least to most
/// permissive.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
enum Access {
    /// `&T` with `T: Freeze`: writing through it is undefined behavior, even in `unsafe` code.
    ReadOnly,
    /// `&mut T`: writable, but only while the path to it is writable too; behind a `&` it can
    /// only be reborrowed as `&`.
    Unique,
    /// A raw pointer, or `&T` with interior mutability: writable however it was reached, since
    /// the pointer can be copied out from behind a shared reference.
    Shared,
}

impl Access {
    fn writable(self) -> bool {
        self != Access::ReadOnly
    }

    /// The access of a pointer with access `self`, followed after reaching it with `path`.
    fn behind(self, path: Access) -> Access {
        match self {
            Access::Unique if path == Access::ReadOnly => Access::ReadOnly,
            access => access,
        }
    }

    /// The access of a new `link` borrow of memory reached with `self`: a borrow cannot grant
    /// more than the path to the memory allows.
    fn reborrow(self, link: Access) -> Access {
        if self == Access::ReadOnly { Access::ReadOnly } else { link }
    }
}

/// What a reference-carrying value may point to.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Target<'tcx> {
    /// A place rooted at a local of this body.
    Place { place: Place<'tcx>, access: Access },
    /// Memory of type `ty` this body cannot name: from an argument, a captured variable, or a
    /// load. It stands for everything reachable from there too.
    Unknown { access: Access, ty: Ty<'tcx> },
}

impl<'tcx> Target<'tcx> {
    fn access(self) -> Access {
        match self {
            Target::Place { access, .. } | Target::Unknown { access, .. } => access,
        }
    }

    fn with_access(self, access: Access) -> Self {
        match self {
            Target::Place { place, .. } => Target::Place { place, access },
            Target::Unknown { ty, .. } => Target::Unknown { access, ty },
        }
    }
}

/// Where a segment starts: the entry, or resuming after the `Yield` ending the given block.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
enum SegmentStart {
    Entry,
    Resume(BasicBlock),
}

/// Where a segment ends: the `Yield` ending the given block, or the return. Ordered as printed:
/// suspension points in block order, which is how `StateTransform` numbers them, then the return.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
enum SegmentEnd {
    Suspend(BasicBlock),
    Return,
}

/// The dataflow state at a program point: what each local may point to.
#[derive(Clone, Default)]
struct State<'tcx> {
    points_to: FxIndexMap<Local, FxIndexSet<Target<'tcx>>>,
}

impl<'tcx> State<'tcx> {
    /// Adds everything in `other`; returns whether `self` grew.
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (local, targets) in &other.points_to {
            changed |= union(self.points_to.entry(*local).or_default(), targets.iter().copied());
        }
        changed
    }
}

/// Writes, with the locations each happens at.
type Writes<'tcx> = FxIndexMap<Write<'tcx>, FxIndexSet<Location>>;

/// A segment: where it may have started, and every write between there and its end.
#[derive(Default)]
struct Segment<'tcx> {
    starts: FxIndexSet<SegmentStart>,
    writes: Writes<'tcx>,
}

/// Adds `from` to `into`; returns whether `into` grew.
fn union<T: Hash + Eq>(into: &mut FxIndexSet<T>, from: impl IntoIterator<Item = T>) -> bool {
    let before = into.len();
    into.extend(from);
    into.len() != before
}

struct WriteSetAnalysis<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    typing_env: TypingEnv<'tcx>,
    /// `pointee_access` results for this body, by type and path.
    access_cache: RefCell<FxHashMap<(Ty<'tcx>, Access), Option<Access>>>,
}

impl<'a, 'tcx> WriteSetAnalysis<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        Self { tcx, body, typing_env: body.typing_env(tcx), access_cache: Default::default() }
    }

    /// Returns every segment, keyed by where it ends, in order. Writes don't affect what any
    /// local points to, so this takes three steps: what each local may point to at the entry of
    /// each block (a fixpoint), each block's writes (recorded once, from that final state), and
    /// the segments each block's writes belong to.
    fn run(&self) -> FxIndexMap<SegmentEnd, Segment<'tcx>> {
        let entry = self.points_to_at_entry();
        let block_writes = self.block_writes(entry);
        self.segments(&block_writes)
    }

    /// What each local may point to at the entry of each block; `None` for blocks never reached.
    fn points_to_at_entry(&self) -> IndexVec<BasicBlock, Option<State<'tcx>>> {
        let blocks = &self.body.basic_blocks;
        let mut entry: IndexVec<BasicBlock, Option<State<'tcx>>> =
            IndexVec::from_elem_n(None, blocks.len());

        // References passed in as arguments (or, for coroutines, captured in the coroutine's
        // state and passed as the resume argument) point to memory this body cannot name.
        let points_to = self
            .body
            .args_iter()
            .map(|arg| (arg, self.pointers_in(self.body.local_decls[arg].ty, Access::Unique)))
            .filter(|(_, pointers)| !pointers.is_empty())
            .collect();
        entry[START_BLOCK] = Some(State { points_to });

        let mut queue: Vec<BasicBlock> = blocks.reverse_postorder().iter().rev().copied().collect();
        let mut queued = DenseBitSet::new_filled(blocks.len());

        while let Some(bb) = queue.pop() {
            queued.remove(bb);
            // A working copy: the entry state itself is kept, to tell whether a later join into
            // it adds anything.
            let Some(mut state) = entry[bb].clone() else { continue };
            self.apply_block(&mut state, None, bb);

            // Joins `state` into the entry of `succ`, queueing it if that grew. The first time a
            // block is reached, `state` becomes its entry: moved if owned, copied if borrowed.
            let mut propagate = |succ: BasicBlock, state: Cow<'_, State<'tcx>>| {
                let changed = match &mut entry[succ] {
                    Some(existing) => existing.join(&state),
                    slot @ None => {
                        *slot = Some(state.into_owned());
                        true
                    }
                };
                if changed && queued.insert(succ) {
                    queue.push(succ);
                }
            };

            // Every edge but the last gets a borrow; the last takes `state`, which is no longer
            // needed. Pointers carry over a `Yield` unchanged: resuming, or being dropped while
            // suspended, continues with the same locals.
            let successors: SmallVec<[BasicBlock; 2]> =
                blocks[bb].terminator().successors().collect();
            if let Some((&last, rest)) = successors.split_last() {
                for &succ in rest {
                    propagate(succ, Cow::Borrowed(&state));
                }
                propagate(last, Cow::Owned(state));
            }
        }

        entry
    }

    /// Each reached block's writes, recorded once from its final entry state; `None` for blocks
    /// never reached. Consumes the entry states, which aren't needed afterwards.
    fn block_writes(
        &self,
        entry: IndexVec<BasicBlock, Option<State<'tcx>>>,
    ) -> IndexVec<BasicBlock, Option<Writes<'tcx>>> {
        entry
            .into_iter_enumerated()
            .map(|(bb, state)| {
                let mut state = state?;
                let mut writes = Writes::default();
                self.apply_block(&mut state, Some(&mut writes), bb);
                Some(writes)
            })
            .collect()
    }

    /// Applies the statements and terminator of `bb` to `state`, recording their writes into
    /// `writes` if given.
    fn apply_block(
        &self,
        state: &mut State<'tcx>,
        mut writes: Option<&mut Writes<'tcx>>,
        bb: BasicBlock,
    ) {
        let data = &self.body.basic_blocks[bb];
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location { block: bb, statement_index };
            self.statement(state, writes.as_deref_mut(), statement, location);
        }
        self.terminator(state, writes, &data.terminator().kind, self.body.terminator_loc(bb));
    }

    /// Collects each segment's writes. A block's writes belong to every segment ending at a
    /// `Yield` or `Return` it reaches without crossing a suspension point, so each segment is
    /// found by walking backwards from its ending blocks, stopping at `Yield`s: reaching one
    /// means the segment can start by resuming from it, which writes its resume argument.
    fn segments(
        &self,
        block_writes: &IndexVec<BasicBlock, Option<Writes<'tcx>>>,
    ) -> FxIndexMap<SegmentEnd, Segment<'tcx>> {
        let blocks = &self.body.basic_blocks;
        let predecessors = blocks.predecessors();
        let reached = |bb: BasicBlock| block_writes[bb].is_some();

        // The blocks each segment ends in: each `Yield` ends its own; every `Return` ends one.
        let mut ends: FxIndexMap<SegmentEnd, Vec<BasicBlock>> = FxIndexMap::default();
        for bb in blocks.indices().filter(|&bb| reached(bb)) {
            let end = match blocks[bb].terminator().kind {
                TerminatorKind::Yield { .. } => SegmentEnd::Suspend(bb),
                TerminatorKind::Return => SegmentEnd::Return,
                _ => continue,
            };
            ends.entry(end).or_default().push(bb);
        }
        ends.sort_keys();

        ends.into_iter()
            .map(|(end, mut stack)| {
                let mut members = DenseBitSet::new_empty(blocks.len());
                let mut resumed_from = DenseBitSet::new_empty(blocks.len());
                while let Some(bb) = stack.pop() {
                    if !members.insert(bb) {
                        continue;
                    }
                    for &pred in predecessors[bb].iter().filter(|&&pred| reached(pred)) {
                        if let TerminatorKind::Yield { .. } = blocks[pred].terminator().kind {
                            resumed_from.insert(pred);
                        } else {
                            stack.push(pred);
                        }
                    }
                }

                let mut segment = Segment::default();
                if members.contains(START_BLOCK) {
                    segment.starts.insert(SegmentStart::Entry);
                }
                for bb in blocks.indices() {
                    if let TerminatorKind::Yield { resume_arg, .. } = blocks[bb].terminator().kind
                        && resumed_from.contains(bb)
                    {
                        segment.starts.insert(SegmentStart::Resume(bb));
                        let write = Write { place: resume_arg, kind: WriteKind::Resume, via: None };
                        let location = self.body.terminator_loc(bb);
                        segment.writes.entry(write).or_default().insert(location);
                    }
                    if members.contains(bb)
                        && let Some(writes) = &block_writes[bb]
                    {
                        for (write, locations) in writes {
                            union(
                                segment.writes.entry(*write).or_default(),
                                locations.iter().copied(),
                            );
                        }
                    }
                }
                (end, segment)
            })
            .collect()
    }

    /// Applies `statement` to `state`, recording its writes into `writes` if given.
    fn statement(
        &self,
        state: &mut State<'tcx>,
        writes: Option<&mut Writes<'tcx>>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.store(state, writes, *place, WriteKind::Store, location);
                let value = self.rvalue_targets(state, rvalue);
                self.assign_targets(state, *place, value);
            }
            StatementKind::SetDiscriminant { place, .. } => {
                self.store(state, writes, **place, WriteKind::Store, location);
            }
            StatementKind::StorageDead(local) => {
                state.points_to.swap_remove(local);
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                // Only writes; a constant destination points to no memory of this body.
                if let Some(writes) = writes
                    && let Operand::Copy(dst) | Operand::Move(dst) = &copy.dst
                {
                    let targets = self.place_value_targets(state, *dst);
                    let unknown = self.pointee_name(dst.local);
                    let kind = WriteKind::ThroughRef;
                    self.record_targets(writes, targets, kind, Some(dst.local), unknown, location);
                }
            }
            _ => {}
        }
    }

    /// Applies the terminator `kind` to `state`, recording its writes into `writes` if given.
    fn terminator(
        &self,
        state: &mut State<'tcx>,
        writes: Option<&mut Writes<'tcx>>,
        kind: &TerminatorKind<'tcx>,
        location: Location,
    ) {
        match kind {
            TerminatorKind::Call { args, destination, .. } => {
                self.call(state, writes, args, Some(*destination), location);
            }
            TerminatorKind::TailCall { args, .. } => self.call(state, writes, args, None, location),
            TerminatorKind::Drop { place, .. } => {
                // Only writes: what any local points to is unchanged.
                let Some(writes) = writes else { return };
                self.store(state, Some(&mut *writes), *place, WriteKind::Drop, location);
                // Drop glue gets `&mut place`, so it may write through references the value holds.
                let held = self.place_value_targets(state, *place);
                let reachable = self.reachable(state, &held);
                let unknown = self.pointee_name(place.local);
                self.record_targets(
                    writes,
                    reachable.into_iter().filter(|&target| self.may_write(target)),
                    WriteKind::CallArg,
                    Some(place.local),
                    unknown,
                    location,
                );
            }
            _ => {}
        }
    }

    fn call(
        &self,
        state: &mut State<'tcx>,
        mut writes: Option<&mut Writes<'tcx>>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Option<Place<'tcx>>,
        location: Location,
    ) {
        let mut all = FxIndexSet::default();
        for Spanned { node: arg, .. } in args {
            // Constants point to no memory of this body.
            let (Operand::Copy(arg) | Operand::Move(arg)) = arg else { continue };
            let targets = self.place_value_targets(state, *arg);
            let reachable = self.reachable(state, &targets);
            if let Some(writes) = writes.as_deref_mut() {
                let unknown = self.pointee_name(arg.local);
                let writable = reachable.iter().copied().filter(|&target| self.may_write(target));
                let kind = WriteKind::CallArg;
                self.record_targets(writes, writable, kind, Some(arg.local), unknown, location);
            }
            all.extend(reachable);
        }
        // The callee may store any pointer it can reach into writable memory it can reach
        // (`mem::swap(&mut p, &mut q)`, `slot.insert(&mut x)`), so each such place that can hold
        // pointers may now also point to anything reachable from the arguments. As in `retype`,
        // a place holding raw or interior-mutable pointers gets them as `Shared`; that set is
        // built at most once per call.
        let mut all_shared = None;
        for &target in &all {
            let Target::Place { place, access } = target else { continue };
            if !access.writable() {
                continue;
            }
            // `pointee_access` is the most permissive access of any pointer in the place's type:
            // `None` if it holds no pointers, so it can't be given any.
            let value = match self.pointee_access(place.ty(self.body, self.tcx).ty, Access::Unique)
            {
                None => continue,
                Some(Access::Shared) => &*all_shared.get_or_insert_with(|| as_shared(&all)),
                Some(_) => &all,
            };
            state.points_to.entry(place.local).or_default().extend(value.iter().copied());
        }
        if let Some(destination) = destination {
            self.store(state, writes, destination, WriteKind::CallResult, location);
            // The return value may point into anything reachable from the arguments.
            let ty = destination.ty(self.body, self.tcx).ty;
            let value = self.retype(all, ty);
            self.assign_targets(state, destination, value);
        }
    }

    /// Records a write to `place` into `writes`, if given, resolving any `Deref` in it through the
    /// points-to sets.
    fn store(
        &self,
        state: &State<'tcx>,
        writes: Option<&mut Writes<'tcx>>,
        place: Place<'tcx>,
        kind: WriteKind,
        location: Location,
    ) {
        let Some(writes) = writes else { return };
        let targets = self.resolve(state, place);
        let (kind, via) = if place.projection.contains(&ProjectionElem::Deref) {
            (WriteKind::ThroughRef, Some(place.local))
        } else {
            (kind, None)
        };
        self.record_targets(writes, targets, kind, via, place, location);
    }

    /// Records a `kind` write, through `via` if any, to each known target, and a `WriteSite` named
    /// `unknown` for unknown memory.
    fn record_targets(
        &self,
        writes: &mut Writes<'tcx>,
        targets: impl IntoIterator<Item = Target<'tcx>>,
        kind: WriteKind,
        via: Option<Local>,
        unknown: Place<'tcx>,
        location: Location,
    ) {
        for target in targets {
            let write = match target {
                Target::Place { place, .. } => Write { place, kind, via },
                Target::Unknown { .. } => Write { place: unknown, kind: WriteKind::WriteSite, via },
            };
            writes.entry(write).or_default().insert(location);
        }
    }

    /// The name for unknown memory reached from `via`: what it points to (`(*_7)`) when it is a
    /// pointer, or `via` itself when the pointers are inside it (a struct, a dropped value,
    /// `ResumeTy`).
    fn pointee_name(&self, via: Local) -> Place<'tcx> {
        if self.body.local_decls[via].ty.builtin_deref(true).is_some() {
            self.tcx.mk_place_deref(Place::from(via))
        } else {
            Place::from(via)
        }
    }

    /// Updates the points-to set of whatever `place` stores into.
    fn assign_targets(
        &self,
        state: &mut State<'tcx>,
        place: Place<'tcx>,
        value: FxIndexSet<Target<'tcx>>,
    ) {
        if place.projection.contains(&ProjectionElem::Deref) {
            // Stored into memory reached through a reference: weakly update the locals it may be.
            for target in self.resolve(state, place) {
                if let Target::Place { place, .. } = target {
                    state.points_to.entry(place.local).or_default().extend(value.iter().copied());
                }
            }
        } else if place.projection.is_empty() {
            // A whole local is overwritten: strong update.
            if value.is_empty() {
                state.points_to.swap_remove(&place.local);
            } else {
                state.points_to.insert(place.local, value);
            }
        } else {
            // A field of a local: the local may now hold these as well.
            state.points_to.entry(place.local).or_default().extend(value);
        }
    }

    fn rvalue_targets(
        &self,
        state: &State<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> FxIndexSet<Target<'tcx>> {
        match rvalue {
            Rvalue::Ref(_, kind, place) => {
                let link = match kind.mutability() {
                    Mutability::Mut => Access::Unique,
                    Mutability::Not
                        if place
                            .ty(self.body, self.tcx)
                            .ty
                            .is_freeze(self.tcx, self.typing_env) =>
                    {
                        Access::ReadOnly
                    }
                    Mutability::Not => Access::Shared,
                };
                self.borrow(state, *place, link)
            }
            // `&raw const` too: whether a raw pointer may be written through depends on where it
            // came from, not on its type.
            Rvalue::RawPtr(_, place) => self.borrow(state, *place, Access::Shared),
            Rvalue::Cast(_, operand, ty) => self.retype(self.operand_targets(state, operand), *ty),
            Rvalue::Use(operand)
            | Rvalue::Repeat(operand, _)
            | Rvalue::WrapUnsafeBinder(operand, _) => self.operand_targets(state, operand),
            Rvalue::CopyForDeref(place) => self.place_value_targets(state, *place),
            Rvalue::Aggregate(_, operands) => {
                operands.iter().flat_map(|operand| self.operand_targets(state, operand)).collect()
            }
            _ => FxIndexSet::default(),
        }
    }

    /// Targets of a `link` borrow of `place` (`&place`, `&mut place`, `&raw place`).
    fn borrow(
        &self,
        state: &State<'tcx>,
        place: Place<'tcx>,
        link: Access,
    ) -> FxIndexSet<Target<'tcx>> {
        self.resolve(state, place)
            .into_iter()
            .map(|target| target.with_access(target.access().reborrow(link)))
            .collect()
    }

    /// `targets` as held by a value of type `ty`. A `&mut` that became a raw pointer (a cast, or
    /// a call returning one) can be copied out from behind a shared reference, so when `ty` may
    /// hold such pointers, `Unique` targets become `Shared`.
    fn retype(&self, targets: FxIndexSet<Target<'tcx>>, ty: Ty<'tcx>) -> FxIndexSet<Target<'tcx>> {
        // `pointee_access` is the most permissive access of any pointer in `ty`. It's `Shared`
        // exactly when `ty` holds a raw pointer or a `&` to interior-mutable data, the pointers
        // that stay writable however they're reached; otherwise `targets` are kept as they are.
        if self.pointee_access(ty, Access::Unique) != Some(Access::Shared) {
            return targets;
        }
        as_shared(&targets)
    }

    /// What the value of an operand may point to.
    fn operand_targets(
        &self,
        state: &State<'tcx>,
        operand: &Operand<'tcx>,
    ) -> FxIndexSet<Target<'tcx>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_value_targets(state, *place),
            // Constants (e.g. references to statics) point to memory outside this body.
            Operand::Constant(_) | Operand::RuntimeChecks(_) => FxIndexSet::default(),
        }
    }

    /// What the value stored at `place` may point to: the points-to sets of the memory it denotes
    /// (tracked per local, not per field).
    fn place_value_targets(
        &self,
        state: &State<'tcx>,
        place: Place<'tcx>,
    ) -> FxIndexSet<Target<'tcx>> {
        let mut out = FxIndexSet::default();
        for target in self.resolve(state, place) {
            match target {
                Target::Place { place, access } => {
                    out.extend(self.held(state, place.local, access));
                }
                Target::Unknown { access, .. } => {
                    out.extend(self.pointers_in(place.ty(self.body, self.tcx).ty, access));
                }
            }
        }
        out
    }

    /// The pointers stored in `local`, followed from memory reached with `path`.
    fn held(
        &self,
        state: &State<'tcx>,
        local: Local,
        path: Access,
    ) -> impl Iterator<Item = Target<'tcx>> {
        let held = state.points_to.get(&local).into_iter().flatten();
        held.map(move |target| target.with_access(target.access().behind(path)))
    }

    /// The memory `place` denotes, with every `Deref` resolved through the points-to sets, and
    /// the access the path through those pointers allows.
    fn resolve(&self, state: &State<'tcx>, place: Place<'tcx>) -> FxIndexSet<Target<'tcx>> {
        // The memory reached through the `Deref`s so far, and where the projection after the last
        // of them starts.
        let mut current = FxIndexSet::from_iter([Target::Place {
            place: Place::from(place.local),
            access: Access::Unique,
        }]);
        let mut start = 0;
        let derefs = place.iter_projections().filter(|&(_, elem)| elem == ProjectionElem::Deref);
        for (pointer, _) in derefs {
            let pointer_ty = pointer.ty(self.body, self.tcx).ty;
            let mut next = FxIndexSet::default();
            for target in current {
                match target {
                    // Points-to sets are per local, so only the base's local matters.
                    Target::Place { place: base, access }
                        if state.points_to.contains_key(&base.local) =>
                    {
                        next.extend(self.held(state, base.local, access));
                    }
                    // A pointer with no recorded origin (e.g. from a constant), or one loaded from
                    // memory this body cannot name.
                    Target::Place { access, .. } | Target::Unknown { access, .. } => {
                        next.insert(self.unknown_behind(pointer_ty, access));
                    }
                }
            }
            current = next;
            start = pointer.projection.len() + 1;
        }

        // Points-to sets are per local, so a base may not have the type the last pointer points
        // to (a pointer cast, or targets of a different field). Only a base of that type takes the
        // rest of the projection; for any other, the write lands somewhere inside the whole base.
        // Projecting regardless would build ill-typed places that can grow without bound in loops.
        let rest = &place.projection[start..];
        let base_ty = PlaceRef { local: place.local, projection: &place.projection[..start] }
            .ty(self.body, self.tcx)
            .ty;
        let ty = place.ty(self.body, self.tcx).ty;
        current
            .into_iter()
            .map(|target| match target {
                Target::Place { place: base, access } => {
                    let place = if base.ty(self.body, self.tcx).ty == base_ty {
                        base.project_deeper(rest, self.tcx)
                    } else {
                        base
                    };
                    Target::Place { place: self.canonicalize(place), access }
                }
                Target::Unknown { access, .. } => Target::Unknown { access, ty },
            })
            .collect()
    }

    /// The unknown memory a pointer of type `pointer_ty`, reached with `path`, points to.
    fn unknown_behind(&self, pointer_ty: Ty<'tcx>, path: Access) -> Target<'tcx> {
        let access = link_access(self.tcx, self.typing_env, pointer_ty).behind(path);
        Target::Unknown { access, ty: pointer_ty.builtin_deref(true).unwrap_or(pointer_ty) }
    }

    /// The unknown memory the pointers in a value of type `ty`, reached with `path`, point to.
    fn pointers_in(&self, ty: Ty<'tcx>, path: Access) -> FxIndexSet<Target<'tcx>> {
        let mut out = FxIndexSet::default();
        pointers_in(self.tcx, self.typing_env, ty, &mut out, 0);
        out.into_iter()
            .map(|(ty, link)| Target::Unknown { access: link.behind(path), ty })
            .collect()
    }

    /// Whether a call given `target` may write to it: its own memory is writable, or, for
    /// unknown memory, a writable pointer is stored inside it.
    fn may_write(&self, target: Target<'tcx>) -> bool {
        match target {
            Target::Place { access, .. } => access.writable(),
            Target::Unknown { access, ty } => {
                access.writable() || self.pointee_access(ty, access).is_some_and(Access::writable)
            }
        }
    }

    /// Everything reachable from `targets` by following the pointers stored there. Read-only
    /// targets are followed too: a `&Cell` or raw pointer stored behind a `&` can be copied out
    /// and written through, so callers filter with `may_write` afterwards.
    fn reachable(
        &self,
        state: &State<'tcx>,
        targets: &FxIndexSet<Target<'tcx>>,
    ) -> FxIndexSet<Target<'tcx>> {
        let mut seen: FxIndexSet<Target<'tcx>> = FxIndexSet::default();
        let mut stack: Vec<Target<'tcx>> = targets.iter().copied().collect();
        while let Some(target) = stack.pop() {
            if !seen.insert(target) {
                continue;
            }
            if let Target::Place { place, access } = target {
                stack.extend(self.held(state, place.local, access));
            }
        }
        seen
    }

    /// The most precise statically identifiable, sized place containing `place` (which has no
    /// `Deref`): follows fields and constant indices, stops at runtime indices and downcasts.
    fn canonicalize(&self, place: Place<'tcx>) -> Place<'tcx> {
        let len = place
            .projection
            .iter()
            .take_while(|elem| {
                matches!(
                    elem,
                    ProjectionElem::Field(..)
                        | ProjectionElem::OpaqueCast(_)
                        | ProjectionElem::UnwrapUnsafeBinder(_)
                        | ProjectionElem::ConstantIndex { from_end: false, .. }
                )
            })
            .count();
        let mut prefix = PlaceRef { local: place.local, projection: &place.projection[..len] };
        while !prefix.ty(self.body, self.tcx).ty.is_sized(self.tcx, self.typing_env)
            && let Some((base, _)) = prefix.last_projection()
        {
            prefix = base;
        }
        Place { local: prefix.local, projection: self.tcx.mk_place_elems(prefix.projection) }
    }

    /// The most any pointer inside a value of type `ty` allows, when the value is reached with
    /// `path`, following pointers nested inside pointees too; `None` if it holds no pointers.
    fn pointee_access(&self, ty: Ty<'tcx>, path: Access) -> Option<Access> {
        if let Some(&known) = self.access_cache.borrow().get(&(ty, path)) {
            return known;
        }
        // Each query starts from an empty table, so a cached result never depends on what an
        // enclosing query assumed about a recursive type.
        let access =
            pointee_access(self.tcx, self.typing_env, ty, path, &mut FxHashMap::default(), 0);
        self.access_cache.borrow_mut().insert((ty, path), access);
        access
    }
}

/// `targets` as held by a raw or interior-mutable pointer: `Unique` targets become `Shared`.
fn as_shared<'tcx>(targets: &FxIndexSet<Target<'tcx>>) -> FxIndexSet<Target<'tcx>> {
    targets
        .iter()
        .map(|&target| match target.access() {
            Access::Unique => target.with_access(Access::Shared),
            _ => target,
        })
        .collect()
}

/// The access a pointer of type `ty` grants to what it points to.
fn link_access<'tcx>(tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>, ty: Ty<'tcx>) -> Access {
    match *ty.kind() {
        ty::Ref(_, _, Mutability::Mut) => Access::Unique,
        ty::Ref(_, inner, Mutability::Not) if inner.is_freeze(tcx, typing_env) => Access::ReadOnly,
        _ if ty.is_box() => Access::Unique,
        // `&T` with interior mutability, raw pointers, and anything else.
        _ => Access::Shared,
    }
}

/// The pointers directly inside a value of type `ty` (not behind another pointer), as their
/// pointee types and the access each grants. A type whose pointers can't be listed (a generic
/// parameter, a trait object, a coroutine, …) stands for itself, with `Shared` access.
fn pointers_in<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    out: &mut FxIndexSet<(Ty<'tcx>, Access)>,
    depth: usize,
) {
    if depth > 16 {
        out.insert((ty, Access::Shared));
        return;
    }
    let visit =
        |ty: Ty<'tcx>, out: &mut FxIndexSet<_>| pointers_in(tcx, typing_env, ty, out, depth + 1);
    match *ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => {}
        ty::FnDef(..) => {}
        ty::Array(elem, _) | ty::Slice(elem) | ty::Pat(elem, _) => visit(elem, out),
        ty::Tuple(elems) => elems.iter().for_each(|elem| visit(elem, out)),
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) => {
            out.insert((inner, link_access(tcx, typing_env, ty)));
        }
        ty::Adt(..) if ty.is_box() => {
            out.insert((ty.expect_boxed_ty(), Access::Unique));
        }
        ty::Adt(def, args) => def.all_fields().for_each(|field| visit(field.ty(tcx, args), out)),
        ty::Closure(_, args) => args.as_closure().upvar_tys().iter().for_each(|ty| visit(ty, out)),
        _ => {
            out.insert((ty, Access::Shared));
        }
    }
}

fn pointee_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    path: Access,
    seen: &mut FxHashMap<(Ty<'tcx>, Access), Option<Access>>,
    depth: usize,
) -> Option<Access> {
    if depth > 16 {
        return Some(Access::Shared);
    }
    if let Some(&known) = seen.get(&(ty, path)) {
        return known;
    }
    // Assume the most while visiting, so recursive types terminate conservatively.
    seen.insert((ty, path), Some(Access::Shared));
    let mut pointers = FxIndexSet::default();
    pointers_in(tcx, typing_env, ty, &mut pointers, 0);
    let result = pointers
        .into_iter()
        .map(|(pointee, link)| {
            // The pointer itself, and whatever is reachable from its pointee.
            let here = link.behind(path);
            let inner = pointee_access(tcx, typing_env, pointee, here, seen, depth + 1);
            inner.map_or(here, |inner| inner.max(here))
        })
        .max();
    seen.insert((ty, path), result);
    result
}

/// Whether `ty` mentions a coroutine. Its layout must not be requested from this pass: the
/// coroutine currently being transformed has none yet, and asking for it is a query cycle
/// (reported as "recursion in an async fn").
fn contains_coroutine<'tcx>(ty: Ty<'tcx>) -> bool {
    ty.walk().any(|arg| {
        matches!(arg.kind(), ty::GenericArgKind::Type(ty) if matches!(ty.kind(), ty::Coroutine(..)))
    })
}

fn print_write_sets<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    segments: &FxIndexMap<SegmentEnd, Segment<'tcx>>,
    coroutine: Option<&LivenessInfo>,
) {
    let names: FxHashMap<Local, Symbol> = body
        .var_debug_info
        .iter()
        .filter_map(|info| match info.value {
            VarDebugInfoContents::Place(place) if place.projection.is_empty() => {
                Some((place.local, info.name))
            }
            _ => None,
        })
        .collect();
    let typing_env = body.typing_env(tcx);
    let source_map = tcx.sess.source_map();

    eprintln!("=== write set: {} ===", tcx.def_path_str(body.source.def_id()));

    // `StateTransform` numbers suspension points in block order.
    let suspension_index = |yield_block: BasicBlock| {
        body.basic_blocks
            .iter_enumerated()
            .filter(|&(bb, data)| {
                bb < yield_block && matches!(data.terminator().kind, TerminatorKind::Yield { .. })
            })
            .count()
    };

    for (&end, segment) in segments {
        let suspension = match end {
            SegmentEnd::Suspend(bb) => Some(suspension_index(bb)),
            SegmentEnd::Return => None,
        };
        let starts = segment
            .starts
            .iter()
            .sorted()
            .map(|start| match start {
                SegmentStart::Entry => "entry".to_string(),
                SegmentStart::Resume(bb) => format!("suspension {}", suspension_index(*bb)),
            })
            .join(" | ");
        let end_text = match suspension {
            Some(index) => {
                let at = coroutine
                    .and_then(|info| info.source_info_at_suspension_points.get(index))
                    .map(|source_info| source_map.span_to_diagnostic_string(source_info.span))
                    .unwrap_or_default();
                format!(
                    "suspension {index} (state {}) at {at}",
                    ty::CoroutineArgs::RESERVED_VARIANTS + index
                )
            }
            None => "return".to_string(),
        };
        eprintln!("segment: {starts} → {end_text}");

        for (write, locations) in &segment.writes {
            let root = write.place.local;
            let name = names.get(&root).map_or("", |name| name.as_str());
            let ty = write.place.ty(body, tcx).ty;
            let size = if contains_coroutine(ty) {
                format!("size_of::<{ty}>()")
            } else {
                match tcx.layout_of(typing_env.as_query_input(ty)) {
                    Ok(layout) => format!("{} B", layout.size.bytes()),
                    Err(_) => format!("size_of::<{ty}>()"),
                }
            };
            let kind = match write.kind {
                WriteKind::Store => "store",
                WriteKind::CallResult => "call result",
                WriteKind::CallArg => "call arg",
                WriteKind::Drop => "drop",
                WriteKind::ThroughRef => "through ref",
                WriteKind::WriteSite => "write site",
                WriteKind::Resume => "resume arg",
            };
            let via = write.via.map(|local| format!(" via {local:?}")).unwrap_or_default();
            let status = status(body, coroutine, suspension, write);
            let sites = locations
                .iter()
                .take(4)
                .map(|location| format!("{location:?}"))
                .chain((locations.len() > 4).then(|| "…".to_string()))
                .join(", ");
            eprintln!(
                "  {:<14} {:<28} {:<12} {:>12}{via}  [{}] → {status}",
                name,
                format!("{:?}", write.place),
                kind,
                size,
                sites,
            );
        }
        if coroutine.is_some() {
            eprintln!("  {:<14} {:<28} {:<12} {:>12}  → always", "", "discriminant", "", "");
        }
    }
}

/// What the written place is, for the output: where it lives and whether it's kept.
fn status<'tcx>(
    body: &Body<'tcx>,
    coroutine: Option<&LivenessInfo>,
    suspension: Option<usize>,
    write: &Write<'tcx>,
) -> Cow<'static, str> {
    let local = write.place.local;
    if write.kind == WriteKind::WriteSite {
        "address at runtime".into()
    } else if local == RETURN_PLACE {
        "return place".into()
    } else if let Some(info) = coroutine {
        if body.args_iter().next() == Some(local) {
            "coroutine state (captured upvars)".into()
        } else if let Some(saved) = info.saved_locals.get(local) {
            match suspension {
                Some(index) => {
                    let live = info.live_locals_at_suspension_points[index].contains(saved);
                    let live = if live { "live here" } else { "not live here" };
                    format!("field _s{}, {live}", saved.as_usize()).into()
                }
                None => format!("field _s{}", saved.as_usize()).into(),
            }
        } else {
            "not saved".into()
        }
    } else if body.args_iter().any(|arg| arg == local) {
        "argument".into()
    } else {
        "local".into()
    }
}
