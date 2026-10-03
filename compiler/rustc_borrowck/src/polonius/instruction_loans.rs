use rustc_data_structures::fx::FxIndexMap;
use rustc_index::bit_set::DenseBitSet;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::{
    Body, BodyLoans, BorrowKind, InstructionLoans, LoanId, Location, Mutability, Place,
    ProjectionElem, StatementId, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{RegionVid, Ty, TyCtxt};
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use super::liveness::LivenessSource;
use super::{
    LoanLivenessVisitor, LocalizedConstraintGraph, LocalizedConstraintGraphVisitor, LocalizedNode,
    PoloniusContext,
};
use crate::RegionInferenceContext;
use crate::borrow_set::BorrowSet;
use crate::dataflow::BorrowIndex;
use crate::universal_regions::UniversalRegions;

/// State for all instructions analyzed this pass
pub(super) struct SiteLoans {
    sites: FxIndexMap<PointIndex, Site>,
}

/// A single instruction's lifetimes and loans reaching it
struct Site {
    id: StatementId,
    /// Lifetimes of the references the instruction uses and whether any loan reached each one
    used: Option<Vec<(RegionVid, bool)>>,
    /// The loans that reached one of those lifetimes here
    loans: DenseBitSet<LoanId>,
}

impl Site {
    fn new(id: StatementId, used: Option<Vec<RegionVid>>, num_loans: usize) -> Self {
        let used = used.map(|used| used.into_iter().map(|region| (region, false)).collect());
        Site { id, used, loans: DenseBitSet::new_empty(num_loans) }
    }
}

impl SiteLoans {
    /// Find all Sites and populate their lifetimes
    fn new<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        universal_regions: &UniversalRegions<'tcx>,
        location_map: &DenseLocationMap,
        num_loans: usize,
    ) -> Self {
        let mut sites = FxIndexMap::default();
        // The lifetimes in a type
        let regions = |ty: Ty<'tcx>| regions_in(tcx, universal_regions, ty);
        // The lifetimes of the last pointer dereferenced for each Place
        let pointer = |place: Place<'tcx>| {
            place
                .iter_projections()
                .rev()
                .find(|(_, elem)| *elem == ProjectionElem::Deref)
                .map_or_else(Vec::new, |(base, _)| regions(base.ty(body, tcx).ty))
        };

        for (block, data) in body.basic_blocks.iter_enumerated() {
            // Add each statement into sites
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let written = match &statement.kind {
                    StatementKind::Assign(assign) => assign.0,
                    StatementKind::SetDiscriminant { place, .. } => **place,
                    _ => continue,
                };
                if written.is_indirect()
                    && let Some(id) = statement.id
                {
                    let point =
                        location_map.point_from_location(Location { block, statement_index });
                    sites.insert(point, Site::new(id, Some(pointer(written)), num_loans));
                }
            }

            // Add the terminator too if it can do a write
            let terminator = data.terminator();
            let Some(id) = terminator.id else { continue };
            let used = match &terminator.kind {
                TerminatorKind::Call { args, destination, .. } => {
                    let mut used = pointer(*destination);
                    used.extend(args.iter().flat_map(|arg| regions(arg.node.ty(body, tcx))));
                    Some(used)
                }
                TerminatorKind::TailCall { args, .. } => {
                    Some(args.iter().flat_map(|arg| regions(arg.node.ty(body, tcx))).collect())
                }
                // A `Drop` impl can reach whatever the dropped value holds references to.
                TerminatorKind::Drop { place, .. } => Some(regions(place.ty(body, tcx).ty)),
                TerminatorKind::Yield { .. } => None,
                _ => continue,
            };
            let point = location_map.point_from_location(body.terminator_loc(block));
            sites.insert(point, Site::new(id, used, num_loans));
        }
        SiteLoans { sites }
    }

    /// Each time Polonius finds a loan, record it in site
    fn record(&mut self, loan: BorrowIndex, node: LocalizedNode) {
        let Some(site) = self.sites.get_mut(&node.point) else { return };
        for (region, reached) in site.used.iter_mut().flatten() {
            if *region == node.region {
                *reached = true;
                site.loans.insert(LoanId::new(loan.index()));
            }
        }
    }
}

/// A traverse function for the borrow checker that also records which loans reach the regions each instruction uses
pub(super) fn traverse<'tcx>(
    graph: &LocalizedConstraintGraph,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    universal_regions: &UniversalRegions<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    location_map: &DenseLocationMap,
    liveness_source: &mut impl LivenessSource,
    visitor: &mut LoanLivenessVisitor<'_>,
) -> Option<SiteLoans> {
    if !tcx.sess.opts.unstable_opts.rad_write_sets {
        graph.traverse(body, borrow_set, location_map, liveness_source, visitor);
        return None;
    }
    let mut site_loans =
        SiteLoans::new(tcx, body, universal_regions, location_map, borrow_set.len());
    let mut recording = Recording { liveness: visitor, site_loans: &mut site_loans };
    graph.traverse(body, borrow_set, location_map, liveness_source, &mut recording);
    Some(site_loans)
}

/// Wrapper for Polonius' liveness visitor
struct Recording<'a, 'b> {
    liveness: &'a mut LoanLivenessVisitor<'b>,
    site_loans: &'a mut SiteLoans,
}

impl LocalizedConstraintGraphVisitor for Recording<'_, '_> {
    fn on_node_traversed(&mut self, loan: BorrowIndex, node: LocalizedNode, is_live: bool) {
        self.liveness.on_node_traversed(loan, node, is_live);
        self.site_loans.record(loan, node);
    }

    fn on_successor_discovered(&mut self, current_node: LocalizedNode, successor: LocalizedNode) {
        self.liveness.on_successor_discovered(current_node, successor);
    }
}

pub(crate) fn instruction_loans<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    regioncx: &RegionInferenceContext<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    polonius_context: Option<&PoloniusContext<'tcx>>,
) -> Option<BodyLoans<'tcx>> {
    if !tcx.sess.opts.unstable_opts.rad_write_sets {
        return None;
    }
    let polonius_context = polonius_context?;
    let universal_regions = regioncx.universal_regions();
    let liveness = regioncx.liveness_constraints();
    let location_map = liveness.location_map();

    // Polonius skips its traversal for bodies without loans; their sites are still needed.
    let own_site_loans;
    let site_loans = match &polonius_context.site_loans {
        Some(site_loans) => site_loans,
        None => {
            own_site_loans =
                SiteLoans::new(tcx, body, universal_regions, location_map, borrow_set.len());
            &own_site_loans
        }
    };
    let loans = loan_table(tcx, borrow_set);
    let from_outside = outside_regions(tcx, body, regioncx);

    let mut instructions = FxIndexMap::default();
    for (&point, site) in &site_loans.sites {
        let mut live = DenseBitSet::new_empty(loans.len());
        for (loan, borrow) in loans.iter_enumerated() {
            // Ignore fake borrows and nonlive ones
            if borrow.is_some() && liveness.is_loan_live_at(BorrowIndex::new(loan.index()), point) {
                live.insert(loan);
            }
        }

        // Build the set of borrows that the pointers in this instruction can hold
        let (reachable, outside) = match &site.used {
            // Suspensions don't write through anything.
            None => (None, false),
            Some(used) => {
                let mut reachable = DenseBitSet::new_empty(loans.len());
                // Filter out fake borrows
                for loan in site.loans.iter().filter(|&loan| loans[loan].is_some()) {
                    reachable.insert(loan);
                }
                // Check if the reference points to memory that we didn't track
                let outside =
                    used.iter().any(|&(region, reached)| !reached || from_outside.contains(region));
                (Some(reachable), outside)
            }
        };
        instructions.insert(site.id, InstructionLoans { live, reachable, outside });
    }
    Some(BodyLoans { loans, instructions })
}

/// Build a map of all loans in the body and the borrow checker's numbering
fn loan_table<'tcx>(
    tcx: TyCtxt<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
) -> IndexVec<LoanId, Option<(Place<'tcx>, Mutability)>> {
    borrow_set
        .iter()
        .map(|loan| {
            // Don't need lifetimes, just the original memory items and whether it's mut
            let place = tcx.erase_and_anonymize_regions(loan.borrowed_place);
            // Ignore fake borrows
            let fake = matches!(loan.kind, BorrowKind::Fake(_));
            (!fake).then_some((place, loan.kind.mutability()))
        })
        .collect()
}

/// Generate a list of regions that memory not borrowed in this body can flow into.
fn outside_regions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    regioncx: &RegionInferenceContext<'tcx>,
) -> DenseBitSet<RegionVid> {
    let universal_regions = regioncx.universal_regions();
    let num_regions = regioncx.definitions.len();
    let mut flows_to: IndexVec<RegionVid, Vec<RegionVid>> =
        IndexVec::from_elem_n(Vec::new(), num_regions);
    for constraint in regioncx.outlives_constraints() {
        flows_to[constraint.sup].push(constraint.sub);
    }
    let mut from_outside = DenseBitSet::new_empty(num_regions);
    let mut stack: Vec<RegionVid> = body
        .args_iter()
        .flat_map(|arg| regions_in(tcx, universal_regions, body.local_decls[arg].ty))
        .chain([universal_regions.fr_static])
        .collect();
    stack.retain(|&region| from_outside.insert(region));
    while let Some(region) = stack.pop() {
        for &next in &flows_to[region] {
            if from_outside.insert(next) {
                stack.push(next);
            }
        }
    }
    from_outside
}

/// The region variables in `ty`, converted as borrowck does for deferred liveness.
fn regions_in<'tcx>(
    tcx: TyCtxt<'tcx>,
    universal_regions: &UniversalRegions<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<RegionVid> {
    let mut regions = Vec::new();
    tcx.for_each_free_region(&ty, |region| {
        if !region.is_bound() && !region.is_erased() {
            regions.push(universal_regions.to_region_vid(region));
        }
    });
    regions
}
