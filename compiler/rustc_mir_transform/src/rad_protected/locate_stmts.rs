use rustc_middle::mir::CheckpointTable;
use rustc_middle::mir::AwaitCheckpoints;
use rustc_middle::mir::Body;
use rustc_middle::mir::StatementId;
use rustc_middle::mir::Location;
use rustc_data_structures::fx::{FxHashSet, FxHashMap};

pub(crate) struct Locations(FxHashMap<StatementId, Location>);

impl Locations {
    pub(crate) fn resolve<'tcx>(table: &CheckpointTable, body: &Body<'tcx>) -> Self {
        let ids: FxHashSet<_> = table.awaits.iter().flat_map(Self::get_ids).collect();
        let mut result: FxHashMap<StatementId, Location> = FxHashMap::default();

        let mut add_location = |id, bb_idx, stmt_idx| {
            let Some(id) = id else {
                return;
            };

            if ids.contains(&id) {
                result.insert(id, Location { 
                    block: bb_idx,
                    statement_index: stmt_idx,
                });
            }
        };

        for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                add_location(stmt.id, bb_idx, stmt_idx);
            }
            add_location(bb_data.terminator().id, bb_idx, bb_data.statements.len());
        }

        Self(result)
    }

    fn get_ids(checkpoints: &AwaitCheckpoints) -> Vec<StatementId> {
        let loop_head = std::iter::once(&checkpoints.loop_head);

        checkpoints.ends
            .iter()
            .chain(loop_head)
            .copied()
            .collect()
    }

    pub(crate) fn get(&self, id: StatementId) -> Result<Location, String> {
        self.0.get(&id).ok_or_else(|| {
            format!("Could not find location for statement with ID {:?}", id)
        }).copied()
    }
}
