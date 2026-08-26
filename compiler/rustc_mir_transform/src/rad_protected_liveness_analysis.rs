use std::collections::VecDeque;

use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::graph::Successors;

use rustc_index::IndexVec;
use rustc_index::bit_set::DenseBitSet;

use rustc_middle::mir::visit::{
    MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor,
};
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BasicBlocks, Body, Local, Location, Place, PlaceRef,
    ProjectionElem, Rvalue, Statement, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{TyCtxt, TypingEnv};

pub(super) struct CheckpointAnalysis<'tcx> {
    pub checkpoints: Vec<(BasicBlock, LivePlaces<'tcx>)>,
}

impl<'tcx> CheckpointAnalysis<'tcx> {
    pub(super) fn analyze(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        Self {
            checkpoints:
                LivenessAnalysis::analyze(tcx, body)
                    .liveness
                    .into_iter_enumerated()
                    .filter(|(bb_idx, _)| Self::is_checkpoint(&body.basic_blocks[*bb_idx]))
                    .map(|(bb_idx, liveness)| (bb_idx, LivePlaces::new(liveness.out)))
                    .collect()
        }
    }

    fn postprocess_gen_kill(bb_data: &BasicBlockData<'_>, gen_kill: &mut GenKill<'tcx>) {
        if Self::is_checkpoint(&bb_data) {
            gen_kill.kill_all = true;
        }
    }

    pub(super) fn is_checkpoint(bb_data: &BasicBlockData<'_>) -> bool {
        matches!(bb_data.terminator().kind, TerminatorKind::Call{..} | TerminatorKind::TailCall{..})
    }
}

pub(super) struct LivePlaces<'tcx> {
    places: Vec<Place<'tcx>>,
}

impl<'tcx> LivePlaces<'tcx> {
    fn new(places: FxHashSet<Place<'tcx>>) -> Self {
        Self {
            places: Self::sort_places(places)
        }
    }

    fn sort_places(set: FxHashSet<Place<'tcx>>) -> Vec<Place<'tcx>> {
        // Values are sorted after being collected into a Vec
        #[allow(rustc::potential_query_instability)]
        let mut places: Vec<Place<'tcx>> = set
            .iter()
            .copied()
            .filter(|place| {
                !set.iter()
                    .any(|other| other != place && other.as_ref().is_prefix_of(place.as_ref()))
            })
            .collect();

        places.sort_by_cached_key(|place| format!("{place:?}"));
        places
    }

    pub(super) fn places(&self) -> &Vec<Place<'tcx>> {
        &self.places
    }
}

struct LivenessAnalysis<'tcx> {
    liveness: IndexVec<BasicBlock, Liveness<'tcx>>,
}

// Liveness Analysis Pass (based on: https://en.wikipedia.org/wiki/Live-variable_analysis)
impl<'tcx> LivenessAnalysis<'tcx> {
    fn analyze(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let gk_analysis = Self::generate_gk_analysis(tcx, &body);
        Self::calculate_liveness(gk_analysis, &body.basic_blocks)
    }

    fn calculate_liveness(gk_analysis: GenKillAnalysis<'tcx>, basic_blocks: &BasicBlocks<'tcx>) -> Self {
        let mut liveness = IndexVec::from_fn_n(
            |_| Liveness::new(),
            basic_blocks.len()
        );
        
        let mut work_queue: VecDeque<BasicBlock> = basic_blocks.indices().rev().collect();
        let mut in_queue = DenseBitSet::new_filled(basic_blocks.len());

        while let Some(bb_idx) = work_queue.pop_front() {
            in_queue.remove(bb_idx);

            let old_in = liveness[bb_idx]._in.clone();
            liveness[bb_idx].out.clear();

            for s in basic_blocks.successors(bb_idx) {
                let successor_in = liveness[s]._in.clone();
                // Order independent since target is unordered (HashSet)
                #[allow(rustc::potential_query_instability)]
                liveness[bb_idx].out.extend(successor_in);
            }

            let gen_kill = &gk_analysis.gen_kill[bb_idx];
            let mut live_in = gen_kill._gen.clone();
            // Order independent since target is unordered (HashSet)
            #[allow(rustc::potential_query_instability)]
            live_in.extend(liveness[bb_idx].out.iter().copied().filter(|&p| !gen_kill.is_killed(p)));
            liveness[bb_idx]._in = live_in;

            if liveness[bb_idx]._in != old_in {
                for &p in basic_blocks.predecessors()[bb_idx].iter() {
                    if in_queue.insert(p) {
                        work_queue.push_back(p);
                    }
                }
            }
        }

        Self { liveness }
    }

    fn generate_gk_analysis(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> GenKillAnalysis<'tcx> {
        let mut gen_kill = IndexVec::<BasicBlock, GenKill<'tcx>>::from_fn_n(
            |_| GenKill::new(),
            body.basic_blocks.len()
        );

        for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
            let mut collector = GenKillCollector::new(tcx, body);

            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                let location = Location {
                    block: bb_idx,
                    statement_index: stmt_idx,
                };

                collector.visit_statement(stmt, location);
            }

            let terminator_location = Location {
                block: bb_idx,
                statement_index: bb_data.statements.len(),
            };

            collector.visit_terminator(bb_data.terminator(), terminator_location);

            gen_kill[bb_idx] = collector.take();

            // Special GenKill postprocessing step to calculate liveness for checkpoints
            // Not found in typical liveness analysis
            CheckpointAnalysis::postprocess_gen_kill(&bb_data, &mut gen_kill[bb_idx]);
        }

        GenKillAnalysis { gen_kill }
    }
}

pub(super) struct Liveness<'tcx> {
    _in: FxHashSet<Place<'tcx>>,
    out: FxHashSet<Place<'tcx>>,
}

impl<'tcx> Liveness<'tcx> {
    fn new() -> Self {
        Self {
            _in: FxHashSet::default(),
            out: FxHashSet::default(),
        }
    }
}

struct GenKillAnalysis<'tcx> {
    gen_kill: IndexVec<BasicBlock, GenKill<'tcx>>,
}


struct GenKillCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    typing_env: TypingEnv<'tcx>,
    gen_kill: GenKill<'tcx>,
}

impl<'a, 'tcx> GenKillCollector<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        Self { tcx, body, typing_env: body.typing_env(tcx), gen_kill: GenKill::new() }
    }

    fn take(self) -> GenKill<'tcx> {
        self.gen_kill
    }

    fn record(&mut self, place: Place<'tcx>, context: PlaceContext) {
        match context {
            // New lifetime or end of lifetime
            PlaceContext::NonUse(NonUseContext::StorageLive | NonUseContext::StorageDead) => {
                self.gen_kill.push_kill(place);
                return;
            }
            
            // Places that aren't actual runtime reads/writes
            PlaceContext::NonUse(_)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::FakeBorrow) => return,

            _ => {}
        }

        // When even the bare Local is still an unsized type
        let Some(canonical) = canonicalize(self.tcx, self.body, self.typing_env, place) else {
            return;
        };

        if !context.is_place_assignment() {
            self.gen_kill.push_gen(canonical);
        } else if canonical == place {
            self.gen_kill.push_kill(canonical);
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for GenKillCollector<'a, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if matches!(statement.kind, StatementKind::FakeRead(..)) {
            return;
        }

        self.super_statement(statement, location);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        self.visit_rvalue(rvalue, location);
        self.visit_place(place, PlaceContext::MutatingUse(MutatingUseContext::Store), location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.visit_projection(place.as_ref(), context, location);
        self.record(*place, context);
    }

    // Handles locals represented directly rather than as an assignment 
    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        self.record(Place::from(local), context);
    }
}

struct GenKill<'tcx> {
    _gen: FxHashSet<Place<'tcx>>,
    // A Vec, not a set, because membership is a prefix test rather than equality
    kill: Vec<Place<'tcx>>,
    kill_all: bool,
}

impl<'tcx> GenKill<'tcx> {
    // A place is killed by a write to itself or to any region that contains it
    fn is_killed(&self, place: Place<'tcx>) -> bool {
        self.kill_all || self.kill.iter().any(|killed| killed.as_ref().is_prefix_of(place.as_ref()))
    }

    fn push_kill(&mut self, place: Place<'tcx>) {
        if !self.kill.contains(&place) {
            self.kill.push(place);
        }
    }
    fn push_gen(&mut self, place: Place<'tcx>) {
        if !self.is_killed(place) {
            self._gen.insert(place);
        }
    }
    fn new() -> Self {
        Self {
            _gen: FxHashSet::default(),
            kill: Vec::new(),
            kill_all: false,
        }
    }
}

// Determines if a Place contains another Place
trait IsPrefixOf<'tcx> {
    fn is_prefix_of(&self, other: PlaceRef<'tcx>) -> bool;
}

impl<'tcx> IsPrefixOf<'tcx> for PlaceRef<'tcx> {
    fn is_prefix_of(&self, other: PlaceRef<'tcx>) -> bool {
        self.local == other.local
            && self.projection.len() <= other.projection.len()
            && self.projection == &other.projection[..self.projection.len()]
    }
}

// Determines what is the most precise Place we can safely checkpoint (we need to 
// ensure it denotes a statically identifiable, sized region suitable for checkpointing)
fn canonicalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: TypingEnv<'tcx>,
    place: Place<'tcx>,
) -> Option<Place<'tcx>> {
    let mut len = 0;

    for (base, elem) in place.iter_projections() {
        let follow = match elem {
            ProjectionElem::Field(..)
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::UnwrapUnsafeBinder(_)
            | ProjectionElem::ConstantIndex { from_end: false, .. } => true,

            ProjectionElem::Deref => base.ty(body, tcx).ty.is_ref(),

            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { from_end: true, .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..) => false,
        };

        if !follow {
            break;
        }

        len += 1;
    }

    let mut prefix = PlaceRef { local: place.local, projection: &place.projection[..len] };

    // The injected checkpoint calls `size_of::<place_ty>()`, so back off to a sized prefix.
    while !prefix.ty(body, tcx).ty.is_sized(tcx, typing_env) {
        prefix = prefix.last_projection()?.0;
    }

    Some(Place { local: prefix.local, projection: tcx.mk_place_elems(prefix.projection) })
}
