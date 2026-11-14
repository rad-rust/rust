use rustc_middle::mir::{
    CheckpointTable, AwaitCheckpoints, StatementId, Location
};
use rustc_middle::mir::Body;
use rustc_data_structures::fx::FxHashMap;

pub(crate) struct Locations(Vec<ResolvedLocations>);

#[derive(Default, Clone)]
pub(crate) struct ResolvedLocations {
    pub loop_head: Option<Location>,
    pub ends: Vec<Location>,
}

impl Locations {
    pub(crate) fn resolve<'tcx>(table: &CheckpointTable, body: &Body<'tcx>) -> Result<Self, String> {
        let mut ids: FxHashMap<_, _> = table
            .awaits
            .iter()
            .enumerate()
            .flat_map(|(idx, checkpoints)| Self::get_ids(idx, checkpoints))
            .collect();

        Self::check_for_duplicates(&ids, table)?;
        
        let mut result = vec![ResolvedLocations::default(); table.awaits.len()];

        let mut add_location = |id, bb_idx, stmt_idx| {
            let Some(id) = id else {
                return;
            };

            let Some((idx, is_loop_head)) = ids.remove(&id) else {
                return;
            };

            let location = Location {
                block: bb_idx,
                statement_index: stmt_idx,
            };

            if is_loop_head {
                result[idx].loop_head = Some(location);
            } else {
                result[idx].ends.push(location);
            }
        };

        for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
            for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
                add_location(stmt.id, bb_idx, stmt_idx);
            }
            add_location(bb_data.terminator().id, bb_idx, bb_data.statements.len());
        }

        if !ids.is_empty() {
            return Err("Some StatementIds from the checkpoint table were not found in MIR".into())
        }
        Ok(Self(result))
    }

    fn get_ids(idx: usize, checkpoints: &AwaitCheckpoints) -> impl Iterator<Item = (StatementId, (usize, bool))> + '_ {
        let loop_head = std::iter::once((checkpoints.loop_head, (idx, true)));

        checkpoints
            .ends
            .iter()
            .map(move |&e| (e, (idx, false)))
            .chain(loop_head)
    }

    fn check_for_duplicates(ids: &FxHashMap<StatementId, (usize, bool)>, table: &CheckpointTable) -> Result<(), String> {
        let expected: usize = table.awaits.iter().map(|a| a.ends.len() + 1).sum();
        if ids.len() != expected {
            return Err("Duplicate StatementIds found in checkpoint table".into());
        }
        Ok(())
    }
    
    pub(crate) fn get(&self, idx: usize) -> &ResolvedLocations {
        &self.0[idx]
    }
}
