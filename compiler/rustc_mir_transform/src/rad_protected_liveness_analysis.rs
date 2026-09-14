use rustc_middle::mir::{BasicBlock, Location, visit::{PlaceContext, Visitor}};
use rustc_middle::mir::{
    Body, BasicBlocks, Local, Place, Rvalue, TerminatorKind, BasicBlockData
};
use std::collections::VecDeque;
use rustc_data_structures::{fx::FxHashSet, graph::Successors};
use rustc_index::{bit_set::DenseBitSet, IndexVec};
use rustc_span::def_id::DefId;
use rustc_span::{sym, Symbol};
use rustc_middle::ty::TyCtxt;

pub(super) struct CheckpointAnalysis {
    pub checkpoints: Vec<(BasicBlock, LiveLocals)>,
}

impl CheckpointAnalysis {
    pub(super) fn analyze<'tcx>(tcx: TyCtxt<'_>, body: &Body<'tcx>) -> Self {
        Self {
            checkpoints:
                LivenessAnalysis::analyze(tcx, body) 
                    .liveness
                    .into_iter_enumerated()
                    .filter(|(bb_idx, _)| Self::is_checkpoint(tcx, &body.basic_blocks[*bb_idx]))
                    .map(|(bb_idx, liveness)| (bb_idx, LiveLocals::new(liveness.out)))
                    .collect()
        }
    }

    fn postprocess_gen_kill<'tcx>(tcx: TyCtxt<'_>, body: &Body<'tcx>, bb_data: &BasicBlockData<'_>, gen_kill: &mut GenKill) {
        if Self::is_checkpoint(tcx, &bb_data) {
            // Order independent since target is unordered (HashSet)
            #[allow(rustc::potential_query_instability)]
            gen_kill.kill.extend(body.local_decls.indices());
        }
    }

    pub(super) fn is_checkpoint(tcx: TyCtxt<'_>, bb_data: &BasicBlockData<'_>) -> bool {
        Self::is_call_to(tcx, bb_data, sym::__checkpoint)
    }

    pub(super) fn is_call_to(tcx: TyCtxt<'_>, bb_data: &BasicBlockData<'_>, symbol: Symbol) -> bool {
        Self::callee_def_id(bb_data).is_some_and(|def_id| tcx.is_diagnostic_item(symbol, def_id))
    }

    fn callee_def_id<'tcx>(bb_data: &BasicBlockData<'tcx>) -> Option<DefId> {
        let func = match &bb_data.terminator().kind {
            TerminatorKind::Call { func, .. }
            | TerminatorKind::TailCall { func, .. } => func,
            _ => return None,
        };
        func.const_fn_def().map(|(def_id, _)| def_id)
    }
}

pub(super) struct LiveLocals {
    locals: Vec<Local>,
}

impl LiveLocals {
    fn new(locals: FxHashSet<Local>) -> Self {
        Self {
            locals: Self::sort_locals(locals)
        }
    }

    fn sort_locals(set: FxHashSet<Local>) -> Vec<Local> {
        // Values are sorted after being collected into a Vec
        #[allow(rustc::potential_query_instability)]
        let mut locals: Vec<Local> = set.into_iter().collect();

        locals.sort();
        locals
    }

    pub(super) fn locals(&self) -> &Vec<Local> {
        &self.locals
    }
}

struct LivenessAnalysis {
    liveness: IndexVec<BasicBlock, Liveness>,
}

// Liveness Analysis Pass (based on: https://en.wikipedia.org/wiki/Live-variable_analysis)
impl LivenessAnalysis {
    fn analyze<'tcx>(tcx: TyCtxt<'_>, body: &Body<'tcx>) -> Self {
        let gk_analysis = Self::generate_gk_analysis(tcx, &body);
        Self::calculate_liveness(gk_analysis, &body.basic_blocks)
    }

    fn calculate_liveness<'tcx>(gk_analysis: GenKillAnalysis, basic_blocks: &BasicBlocks<'tcx>) -> Self {
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

            let mut live_in = gk_analysis.gen_kill[bb_idx]._gen.clone();
            // Order independent since target is unordered (HashSet)
            #[allow(rustc::potential_query_instability)]
            live_in.extend(liveness[bb_idx].out.difference(&gk_analysis.gen_kill[bb_idx].kill));
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

    fn generate_gk_analysis<'tcx>(tcx: TyCtxt<'_>, body: &Body<'tcx>) -> GenKillAnalysis {
        let mut gen_kill = IndexVec::<BasicBlock, GenKill>::from_fn_n(
            |_| GenKill::new(),
            body.basic_blocks.len()
        );

        for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
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

            // Special GenKill postprocessing step to calculate liveness for checkpoints
            // Not found in typical liveness analysis
            CheckpointAnalysis::postprocess_gen_kill(tcx, body, &bb_data, &mut gen_kill[bb_idx]);
        }

        GenKillAnalysis { gen_kill }
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
