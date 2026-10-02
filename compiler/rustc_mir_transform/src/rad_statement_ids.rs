use either::Either;
use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::mir::{Body, Location, StatementId, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use crate::PassPolicy;

/// Numbers every statement and terminator before borrowck clones the body, so borrowck's
/// results can be attached to exactly the same instructions in later MIR.
pub(super) struct RadStatementIds;

impl<'tcx> crate::MirPass<'tcx> for RadStatementIds {
    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(ctx.opts.unstable_opts.rad_write_sets)
    }

    fn run_pass(&self, _tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut ids = (0..).map(StatementId::from_usize);
        for data in body.basic_blocks.as_mut_preserves_cfg() {
            for statement in &mut data.statements {
                statement.id = ids.next();
            }
            data.terminator_mut().id = ids.next();
        }
    }
}

/// The id of the statement or terminator at `location`, as printed.
pub(super) fn id_label(body: &Body<'_>, location: Location) -> String {
    match body.stmt_at(location) {
        Either::Left(statement) => statement.id,
        Either::Right(terminator) => terminator.id,
    }
    .map_or_else(|| "-".to_string(), |id| format!("{id:?}"))
}

/// Find ids are shared by more than one instruction
pub(super) fn repeated_ids(body: &Body<'_>) -> (usize, usize) {
    let mut carriers: FxIndexMap<StatementId, (usize, bool)> = FxIndexMap::default();
    for data in body.basic_blocks.iter() {
        let terminator = data.terminator();
        let elaborated = matches!(
            terminator.kind,
            TerminatorKind::Drop { .. } | TerminatorKind::Call { .. } | TerminatorKind::Goto { .. }
        );
        let ids = data.statements.iter().map(|statement| (statement.id, false));
        for (id, elaborated) in ids.chain([(terminator.id, elaborated)]) {
            if let Some(id) = id {
                let (count, all_elaborated) = carriers.entry(id).or_insert((0, true));
                *count += 1;
                *all_elaborated &= elaborated;
            }
        }
    }
    let (mut shared, mut duplicated) = (0, 0);
    for &(count, all_elaborated) in carriers.values() {
        if count > 1 {
            if all_elaborated {
                shared += 1;
            } else {
                duplicated += 1;
            }
        }
    }
    (shared, duplicated)
}

/// Find statements and terminators that have no id
pub(super) fn unnumbered(body: &Body<'_>) -> Vec<Location> {
    let mut locations = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            if statement.id.is_none() {
                locations.push(Location { block, statement_index });
            }
        }
        if data.terminator().id.is_none() {
            locations.push(body.terminator_loc(block));
        }
    }
    locations
}
