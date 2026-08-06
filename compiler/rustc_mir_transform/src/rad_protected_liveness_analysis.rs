use rustc_middle::mir::{BasicBlock, Location, visit::{PlaceContext, Visitor}};
use rustc_middle::mir::{
    Body, BasicBlocks, Local, Place, Rvalue
};
use std::ops::{Deref, DerefMut};
use std::collections::VecDeque;
use rustc_data_structures::{fx::FxHashSet, graph::Successors};
use rustc_index::IndexVec;

pub(super) struct LivenessAnalysis {
    liveness: IndexVec<BasicBlock, Liveness>,
}

// Liveness Analysis Pass (based on: https://en.wikipedia.org/wiki/Live-variable_analysis)
impl LivenessAnalysis {
    pub(super) fn analyze<'tcx>(body: &Body<'tcx>) -> Self {
        let gk_analysis = Self::generate_gk_analysis(&body.basic_blocks);
        Self::calculate_liveness(gk_analysis, &body.basic_blocks)
    }

    fn calculate_liveness<'tcx>(gk_analysis: GenKillAnalysis, basic_blocks: &BasicBlocks<'tcx>) -> Self {
        let mut liveness = IndexVec::from_fn_n(
            |_| Liveness::new(),
            basic_blocks.len()
        );
        
        let mut work_queue: VecDeque<BasicBlock> = basic_blocks.indices().collect();

        while !work_queue.is_empty() {
            let bb_idx = work_queue.pop_front().unwrap();

            let old_in = liveness[bb_idx]._in.clone();
            liveness[bb_idx].out.clear();

            for s in basic_blocks.successors(bb_idx) {
                let successor_in = liveness[s]._in.clone();
                // Order independent since target is unordered (HashSet)
                #[allow(rustc::potential_query_instability)]
                liveness[bb_idx].out.extend(successor_in);
            }

            let mut live_in = gk_analysis.gen_kill[bb_idx]._gen.clone();
            // Order independent since target is unordered (HashSet)
            #[allow(rustc::potential_query_instability)]
            live_in.extend(liveness[bb_idx].out.difference(&gk_analysis.gen_kill[bb_idx].kill));
            liveness[bb_idx]._in = live_in;

            if liveness[bb_idx]._in != old_in {
                for p in basic_blocks.predecessors()[bb_idx].clone() {
                    work_queue.push_back(p);
                }
            }
        }

        Self { liveness }
    }

    fn generate_gk_analysis<'tcx>(basic_blocks: &BasicBlocks<'tcx>) -> GenKillAnalysis {
        let mut gen_kill = IndexVec::<BasicBlock, GenKill>::from_fn_n(
            |_| GenKill::new(),
            basic_blocks.len()
        );

        for (bb_idx, bb_data) in basic_blocks.iter_enumerated() {
            let mut collector = GenKillCollector::new();

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
        }

        GenKillAnalysis { gen_kill }
    }

}

impl Deref for LivenessAnalysis {
    type Target = IndexVec<BasicBlock, Liveness>;

    fn deref(&self) -> &Self::Target {
        &self.liveness
    }
}

impl DerefMut for LivenessAnalysis {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.liveness
    }
}

pub(super) struct Liveness {
    _in: FxHashSet<Local>,
    out: FxHashSet<Local>,
}

impl Liveness {
    fn new() -> Self {
        Self {
            _in: FxHashSet::default(),
            out: FxHashSet::default(),
        }
    }

    pub(super) fn _in(&self) -> &FxHashSet<Local> {
        &self._in
    }
    pub(super) fn out(&self) -> &FxHashSet<Local> {
        &self.out
    }
}

struct GenKillAnalysis {
    gen_kill: IndexVec<BasicBlock, GenKill>,
}


struct GenKillCollector {
    gen_kill: GenKill,
}

impl GenKillCollector {
    fn new() -> Self {
        Self { gen_kill: GenKill::new() }
    }

    fn take(self) -> GenKill {
        self.gen_kill
    }
}

impl<'tcx> Visitor<'tcx> for GenKillCollector {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        
        if context.is_place_assignment() {
            self.gen_kill.push_kill(local);
        }
        else if context.is_mutating_use() {
            self.gen_kill.push_gen(local);
            // The push_kill is not strictly necessary here, but it follows the convention
            // of kill marking all writes (not just writes before a use)
            self.gen_kill.push_kill(local);

        }
        else if context.is_use() {
            self.gen_kill.push_gen(local);
        }
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        self.visit_rvalue(rvalue, location);
        self.gen_kill.push_kill(place.local);
    }
}

struct GenKill {
    _gen: FxHashSet<Local>,
    kill: FxHashSet<Local>,
}

impl GenKill {
    fn push_kill(&mut self, local: Local) {
        self.kill.insert(local);
    }
    fn push_gen(&mut self, local: Local) {
        if !self.kill.contains(&local) {
            self._gen.insert(local);
        }
    }
    fn new() -> Self {
        Self {
            _gen: FxHashSet::default(),
            kill: FxHashSet::default(),
        }
    }
}
