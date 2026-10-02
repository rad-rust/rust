use rustc_data_structures::fx::FxIndexMap;
use rustc_index::IndexVec;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{
    Body, BodyLoans, BorrowKind, LoanId, Location, StatementKind, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;

use super::PoloniusContext;
use crate::RegionInferenceContext;
use crate::borrow_set::BorrowSet;

/// Produce a table of the body's loans with the set of live loans at each instruction
pub(crate) fn statement_live_loans<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    regioncx: &RegionInferenceContext<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    polonius_context: Option<&PoloniusContext<'tcx>>,
) -> Option<BodyLoans<'tcx>> {
    if !tcx.sess.opts.unstable_opts.rad_write_sets || polonius_context.is_none() {
        return None;
    }

    // Create a list of all borrows, skipping Polonius-generated ones
    let mut loans = IndexVec::new();
    let loan_ids: Vec<_> = borrow_set
        .iter_enumerated()
        .filter(|(_, loan)| !matches!(loan.kind, BorrowKind::Fake(_)))
        .map(|(index, loan)| {
            // Record only the original memory items and whether it's mut
            let place = tcx.erase_and_anonymize_regions(loan.borrowed_place);
            (index, loans.push((place, loan.kind.mutability())))
        })
        .collect();

    let liveness = regioncx.liveness_constraints();
    let location_map = liveness.location_map();
    let live_at = |location: Location| {
        let point = location_map.point_from_location(location);
        let mut live = DenseBitSet::<LoanId>::new_empty(loans.len());
        for &(index, id) in &loan_ids {
            if liveness.is_loan_live_at(index, point) {
                live.insert(id);
            }
        }
        live
    };

    let mut live = FxIndexMap::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        // Use polonius' alias analysis for statements that write through a pointer
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let written = match &statement.kind {
                StatementKind::Assign(assign) => assign.0,
                StatementKind::SetDiscriminant { place, .. } => **place,
                _ => continue,
            };
            if written.is_indirect()
                && let Some(id) = statement.id
            {
                live.insert(id, live_at(Location { block, statement_index }));
            }
        }

        // Terminators can write to values live during the Terminator
        let terminator = data.terminator();
        if let TerminatorKind::Call { .. }
        | TerminatorKind::TailCall { .. }
        | TerminatorKind::Drop { .. }
        | TerminatorKind::Yield { .. } = terminator.kind
            && let Some(id) = terminator.id
        {
            live.insert(id, live_at(body.terminator_loc(block)));
        }
    }
    Some(BodyLoans { loans, live })
}
