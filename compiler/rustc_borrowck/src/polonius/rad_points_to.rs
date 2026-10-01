use rustc_middle::mir::{Body, BorrowKind, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt};

use super::PoloniusContext;
use crate::RegionInferenceContext;
use crate::borrow_set::BorrowSet;

pub(crate) fn dump_rad_points_to<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    regioncx: &RegionInferenceContext<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    polonius_context: Option<&PoloniusContext<'tcx>>,
) {
    if !tcx.sess.opts.unstable_opts.rad_polonius_points_to {
        return;
    }

    ty::print::with_no_trimmed_paths!({
        let def_path = tcx.def_path_str(body.source.def_id());
        if polonius_context.is_none() {
            eprintln!("=== polonius live loans: {def_path} === (needs `-Zpolonius=next`)");
            return;
        }
        eprintln!("=== polonius live loans: {def_path} ===");
        let liveness = regioncx.liveness_constraints();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            let what = match &data.terminator().kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                    format!("call {func:?}")
                }
                TerminatorKind::Yield { .. } => "suspension".to_string(),
                _ => continue,
            };
            let location = body.terminator_loc(bb);
            let point = liveness.location_map().point_from_location(location);
            let live: Vec<String> = borrow_set
                .iter_enumerated()
                .filter(|&(index, loan)| {
                    // Fake borrows only exist for borrowck; they're not pointers.
                    !matches!(loan.kind, BorrowKind::Fake(_))
                        && liveness.is_loan_live_at(index, point)
                })
                .map(|(_, loan)| format!("{:?}", loan.borrowed_place))
                .collect();
            eprintln!("  {location:?} {what}: {{{}}}", live.join(", "));
        }
    });
}
