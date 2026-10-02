use rustc_middle::mir::{
    Body, BorrowKind, LiveLoansTerminatorKind, TerminatorKind, TerminatorLiveLoans,
};
use rustc_middle::ty::TyCtxt;

use super::PoloniusContext;
use crate::RegionInferenceContext;
use crate::borrow_set::BorrowSet;

pub(crate) fn terminator_live_loans<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    regioncx: &RegionInferenceContext<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    polonius_context: Option<&PoloniusContext<'tcx>>,
) -> Option<Vec<TerminatorLiveLoans<'tcx>>> {
    if !tcx.sess.opts.unstable_opts.rad_write_sets || polonius_context.is_none() {
        return None;
    }
    let liveness = regioncx.liveness_constraints();
    let location_map = liveness.location_map();
    let points = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(bb, data)| {
            let terminator = data.terminator();
            let kind = match terminator.kind {
                TerminatorKind::Call { .. } | TerminatorKind::TailCall { .. } => {
                    LiveLoansTerminatorKind::Call
                }
                TerminatorKind::Yield { .. } => LiveLoansTerminatorKind::Yield,
                _ => return None,
            };
            let point = location_map.point_from_location(body.terminator_loc(bb));
            let loans = borrow_set
                .iter_enumerated()
                .filter(|&(index, loan)| {
                    // Ignore fake borrows and nonlive ones
                    !matches!(loan.kind, BorrowKind::Fake(_))
                        && liveness.is_loan_live_at(index, point)
                })
                // Don't need lifetimes, just the original memory items and whether it's mut
                .map(|(_, loan)| {
                    (tcx.erase_and_anonymize_regions(loan.borrowed_place), loan.kind.mutability())
                })
                .collect();
            Some(TerminatorLiveLoans { kind, span: terminator.source_info.span, loans })
        })
        .collect();
    Some(points)
}
