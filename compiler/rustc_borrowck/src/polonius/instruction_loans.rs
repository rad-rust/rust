use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::fx::{FxHashSet, FxIndexMap};
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_index::bit_set::DenseBitSet;
use rustc_index::{Idx, IndexVec};
use rustc_middle::hir::nested_filter;
use rustc_middle::mir::{
    Body, BodyLoans, BorrowKind, InstructionLoans, LoanId, Location, Mutability, Operand,
    OutsideKind, Place, ProjectionElem, RadWriteSummary, StatementId, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::{self, GenericArgKind, RegionVid, Ty, TyCtxt, TypeVisitableExt};
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
    /// Lifetimes of the references the instruction uses
    used: Option<Vec<Used>>,
    /// The loans that reached one of those lifetimes here
    loans: DenseBitSet<LoanId>,
    /// Whether the instruction is a call that used the callee's summary
    summary: bool,
    /// For such a call: the memory that the callee also writes, that none of the arguments lead to
    other: Option<OutsideKind>,
}

impl Site {
    fn new(id: StatementId, used: Option<Vec<Used>>, num_loans: usize) -> Self {
        Site { id, used, loans: DenseBitSet::new_empty(num_loans), summary: false, other: None }
    }
}

/// A lifetime that an instruction uses
struct Used {
    region: RegionVid,
    /// The memory behind it, for when that memory isn't borrowed in this body
    kind: OutsideKind,
    /// The lifetimes in the type behind it
    inner: Vec<RegionVid>,
    /// Whether any loan reached it
    reached: bool,
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
        // The lifetimes in a type, with the memory behind each
        let uses = |ty: Ty<'tcx>| {
            let mut uses = RegionUses::new(tcx, body, universal_regions);
            uses.walk(ty, false);
            // Lifetimes that the walk didn't reach, such as a coroutine's parent lifetimes that no
            // upvar holds, still need their loans
            for region in regions(ty) {
                if !uses.found.iter().any(|used| used.region == region) {
                    uses.push(region, OutsideKind::Unknown, Vec::new());
                }
            }
            uses.found
        };
        // The lifetimes of the last pointer dereferenced for each Place
        let pointer = |place: Place<'tcx>| {
            place
                .iter_projections()
                .rev()
                .find(|(_, elem)| *elem == ProjectionElem::Deref)
                .map_or_else(Vec::new, |(base, _)| {
                    let ty = base.ty(body, tcx).ty;
                    let mut uses = RegionUses::new(tcx, body, universal_regions);
                    match *ty.kind() {
                        // If this is a reference, use the type of the reference target
                        ty::Ref(region, inner, mutability) => {
                            uses.reference(region, inner, mutability, false)
                        }
                        _ => uses.all(ty, OutsideKind::Unknown),
                    }
                    uses.found
                })
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
            let mut summary_used = None;
            let used = match &terminator.kind {
                // Use the callee's write summary if it has one, or else every lifetime in the
                // arguments
                TerminatorKind::Call { func, args, destination, .. } => {
                    let mut used = pointer(*destination);
                    let arg_regions: Vec<RegionVid> =
                        args.iter().flat_map(|arg| regions(arg.node.ty(body, tcx))).collect();
                    let arg_uses = args.iter().flat_map(|arg| uses(arg.node.ty(body, tcx)));
                    match callee_summary(tcx, body, func)
                        .filter(|summary| summary.written.domain_size() == arg_regions.len())
                    {
                        // Only the lifetimes the callee writes through. The summary numbers them
                        // in `regions_in` order, so match them by region.
                        Some(summary) => {
                            let written: FxHashSet<RegionVid> = arg_regions
                                .into_iter()
                                .enumerate()
                                .filter(|&(k, _)| summary.written.contains(k))
                                .map(|(_, region)| region)
                                .collect();
                            used.extend(arg_uses.filter(|used| written.contains(&used.region)));
                            summary_used = Some(summary.other);
                        }
                        None => used.extend(arg_uses),
                    }
                    Some(used)
                }
                TerminatorKind::TailCall { args, .. } => {
                    Some(args.iter().flat_map(|arg| uses(arg.node.ty(body, tcx))).collect())
                }
                // A `Drop` impl can reach whatever the dropped value holds references to.
                TerminatorKind::Drop { place, .. } => Some(uses(place.ty(body, tcx).ty)),
                TerminatorKind::Yield { .. } => None,
                _ => continue,
            };
            let point = location_map.point_from_location(body.terminator_loc(block));
            let mut site = Site::new(id, used, num_loans);
            if let Some(other) = summary_used {
                site.summary = true;
                site.other = other;
            }
            sites.insert(point, site);
        }
        SiteLoans { sites }
    }

    /// Each time Polonius finds a loan, record it in site
    fn record(&mut self, loan: BorrowIndex, node: LocalizedNode) {
        let Some(site) = self.sites.get_mut(&node.point) else { return };
        for used in site.used.iter_mut().flatten() {
            if used.region == node.region {
                used.reached = true;
                site.loans.insert(LoanId::new(loan.index()));
            }
        }
    }
}

/// A traverse functio that also records which loans reach the regions each instruction uses
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
    if !tcx.rad_checkpointed(body.source.def_id()) {
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
    if !tcx.rad_checkpointed(body.source.def_id()) {
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
    // Link each lifetime to the lifetimes whose references can flow into it
    let mut flows_from = IndexVec::from_elem_n(Vec::new(), regioncx.definitions.len());
    for constraint in regioncx.outlives_constraints() {
        flows_from[constraint.sub].push(constraint.sup);
    }
    let sources = source_regions(tcx, body, universal_regions, regioncx.definitions.len());

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
            None => (None, None),
            Some(used) => {
                let mut reachable = DenseBitSet::new_empty(loans.len());
                // Filter out fake borrows
                for loan in site.loans.iter().filter(|&loan| loans[loan].is_some()) {
                    reachable.insert(loan);
                }
                // Check if the reference points to memory that we didn't track, and what kind
                let outside = used
                    .iter()
                    .filter(|used| {
                        !used.reached || flows_in(&flows_from, &sources, used.region, &used.inner)
                    })
                    .map(|used| used.kind)
                    .chain(site.other)
                    .max();
                (Some(reachable), outside)
            }
        };
        let summary = site.summary;
        instructions.insert(site.id, InstructionLoans { live, reachable, outside, summary });
    }

    // Only a fn's own body is called directly. Closures and `async` blocks are called through
    // traits, which have no summary.
    let def = body.source.def_id();
    let summary = (body.coroutine.is_none() && !tcx.is_typeck_child(def))
        .then(|| write_summary(tcx, body, regioncx, site_loans, &from_outside, &flows_from));
    Some(BodyLoans { loans, instructions, summary })
}

/// Generates the write summary of this body, which lists the lifetimes of its arguments that it writes through.
fn write_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    regioncx: &RegionInferenceContext<'tcx>,
    site_loans: &SiteLoans,
    from_outside: &DenseBitSet<RegionVid>,
    flows_from: &IndexVec<RegionVid, Vec<RegionVid>>,
) -> RadWriteSummary {
    let universal_regions = regioncx.universal_regions();
    let params: Vec<RegionVid> = body
        .args_iter()
        .flat_map(|arg| regions_in(tcx, universal_regions, body.local_decls[arg].ty))
        .collect();
    let num_regions = regioncx.definitions.len();
    let mut statics = DenseBitSet::new_empty(num_regions);
    statics.insert(universal_regions.fr_static);

    // From the lifetimes that each site writes through, find memory that the caller can't name
    let mut written = DenseBitSet::new_empty(num_regions);
    let mut stack = Vec::new();
    let mut other = None;
    for site in site_loans.sites.values() {
        other = other.max(site.other);
        for used in site.used.iter().flatten() {
            // Neither a loan of this body nor an argument, or `'static`: memory that the caller
            // can't name
            if !used.reached && !from_outside.contains(used.region)
                || flows_in(flows_from, &statics, used.region, &used.inner)
            {
                other = other.max(Some(used.kind));
            }
            if written.insert(used.region) {
                stack.push(used.region);
            }
        }
    }

    // Mark every lifetime whose references can flow into a written one
    while let Some(region) = stack.pop() {
        for &source in &flows_from[region] {
            if written.insert(source) {
                stack.push(source);
            }
        }
    }

    // Match these regions to the original arguments
    let mut written_params = DenseBitSet::new_empty(params.len());
    for (k, &region) in params.iter().enumerate() {
        if written.contains(region) {
            written_params.insert(k);
        }
    }
    RadWriteSummary { written: written_params, other }
}

/// Provider for `rad_write_summary`
pub(crate) fn rad_write_summary(tcx: TyCtxt<'_>, def: LocalDefId) -> Option<&RadWriteSummary> {
    if !matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        || !tcx.rad_checkpointed(def.to_def_id())
    {
        return None;
    }
    tcx.mir_borrowck(def).ok()?.loans.get(&def)?.summary.as_ref()
}

/// The summary of the fn that `func` calls, if the call site can use it
fn callee_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
) -> Option<&'tcx RadWriteSummary> {
    let (callee, args) = func.const_fn_def()?;
    // Which impl a trait method calls is only known after monomorphization
    if tcx.trait_of_assoc(callee).is_some() {
        return None;
    }
    // A type parameter can be a reference, which the generic body can't see writes through
    if args
        .iter()
        .any(|arg| !matches!(arg.kind(), GenericArgKind::Lifetime(_)) && arg.has_free_regions())
    {
        return None;
    }

    if let Some(local) = callee.as_local() {
        if !tcx.rad_checkpointed(callee) {
            return None;
        }
        // A fn in another crate can't call back into this one. A local one is only used if it
        // can't reach this body, since its summary needs its borrowck to finish first.
        let root = tcx.typeck_root_def_id_local(body.source.def_id().expect_local());
        if reaches(tcx, local, root) {
            return None;
        }
    }

    tcx.rad_write_summary(callee)
}

/// Whether `from` can call `to` through direct calls of local `#[rad::checkpoint]` fns, which are
/// the calls that use a summary
fn reaches(tcx: TyCtxt<'_>, from: LocalDefId, to: LocalDefId) -> bool {
    let mut seen = FxHashSet::default();
    let mut stack = vec![from];
    while let Some(def) = stack.pop() {
        if def == to {
            return true;
        }
        if !seen.insert(def) {
            continue;
        }
        let Some(hir_body) = tcx.hir_maybe_body_owned_by(def) else { continue };
        let mut callees = Callees { tcx, typeck: tcx.typeck(def), found: Vec::new() };
        callees.visit_body(hir_body);
        stack.extend(callees.found);
    }
    false
}

/// Collects the local `#[rad::checkpoint]` fns that a body and its closures call directly
struct Callees<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    found: Vec<LocalDefId>,
}

impl<'tcx> Visitor<'tcx> for Callees<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        let callee: Option<DefId> = match expr.kind {
            hir::ExprKind::Call(func, _) => match *self.typeck.expr_ty_adjusted(func).kind() {
                ty::FnDef(def_id, _) => Some(def_id),
                _ => None,
            },
            hir::ExprKind::MethodCall(..) => self.typeck.type_dependent_def_id(expr.hir_id),
            _ => None,
        };
        if let Some(callee) = callee
            && let Some(local) = callee.as_local()
            && self.tcx.rad_checkpointed(callee)
        {
            self.found.push(local);
        }
        intravisit::walk_expr(self, expr);
    }
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
    let num_regions = regioncx.definitions.len();
    let mut flows_to: IndexVec<RegionVid, Vec<RegionVid>> =
        IndexVec::from_elem_n(Vec::new(), num_regions);
    for constraint in regioncx.outlives_constraints() {
        flows_to[constraint.sup].push(constraint.sub);
    }
    let mut from_outside = source_regions(tcx, body, regioncx.universal_regions(), num_regions);
    let mut stack: Vec<RegionVid> = from_outside.iter().collect();
    while let Some(region) = stack.pop() {
        for &next in &flows_to[region] {
            if from_outside.insert(next) {
                stack.push(next);
            }
        }
    }
    from_outside
}

/// The lifetimes of memory not borrowed in this body: the arguments' and `'static`
fn source_regions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    universal_regions: &UniversalRegions<'tcx>,
    num_regions: usize,
) -> DenseBitSet<RegionVid> {
    let mut sources = DenseBitSet::new_empty(num_regions);
    for arg in body.args_iter() {
        for region in regions_in(tcx, universal_regions, body.local_decls[arg].ty) {
            sources.insert(region);
        }
    }
    sources.insert(universal_regions.fr_static);
    sources
}

/// Whether a reference from `sources` can flow into `region`, the lifetime of a reference to a
/// type with the lifetimes `inner`.
fn flows_in(
    flows_from: &IndexVec<RegionVid, Vec<RegionVid>>,
    sources: &DenseBitSet<RegionVid>,
    region: RegionVid,
    inner: &[RegionVid],
) -> bool {
    // TODO: This misses a reference from outside whose type also holds its own lifetime, like
    // `&'static mut Foo<'static>`. For `&'r T` to be well-formed, every lifetime in `T` must
    // outlive `'r`, so a loan of a local whose type holds a `'static` has `'static` flowing
    // into `'r`. Such a path says where the memory behind `T`'s own references came from, and
    // that memory is its own `Used`. So the search skips `inner` and every lifetime that flows
    // into them.
    let mut behind = DenseBitSet::new_empty(flows_from.len());
    let mut stack: Vec<RegionVid> = inner.iter().copied().filter(|&r| behind.insert(r)).collect();
    while let Some(next) = stack.pop() {
        for &source in &flows_from[next] {
            if behind.insert(source) {
                stack.push(source);
            }
        }
    }

    let mut seen = DenseBitSet::new_empty(flows_from.len());
    seen.insert(region);
    let mut stack = vec![region];
    while let Some(next) = stack.pop() {
        if sources.contains(next) {
            return true;
        }
        for &source in &flows_from[next] {
            if !behind.contains(source) && seen.insert(source) {
                stack.push(source);
            }
        }
    }
    false
}

/// Finds the lifetimes in a type and the kind of memory behind each
struct RegionUses<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    universal_regions: &'a UniversalRegions<'tcx>,
    /// The typeck root of the body
    root: LocalDefId,
    /// Types already walked, and whether they were behind a shared reference
    seen: FxHashSet<(Ty<'tcx>, bool)>,
    found: Vec<Used>,
}

impl<'a, 'tcx> RegionUses<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        universal_regions: &'a UniversalRegions<'tcx>,
    ) -> Self {
        let typing_env = body.typing_env(tcx);
        let root = tcx.typeck_root_def_id_local(body.source.def_id().expect_local());
        RegionUses {
            tcx,
            typing_env,
            universal_regions,
            root,
            seen: FxHashSet::default(),
            found: Vec::new(),
        }
    }

    /// Records each lifetime in `ty` with what kind of memory it holds:
    ///
    /// | Lifetime origin                          | Kind      |
    /// |------------------------------------------|-----------|
    /// | `&'r mut T`, not behind a shared ref     | Exclusive |
    /// | `&'r T`, `T: Freeze`                     | ReadOnly  |
    /// | `&'r T`, `T: !Freeze`; any `Context`     | Kernel    |
    /// | `PhantomData`, a fn item, or not named   | Token     |
    /// |   by the value a closure or future holds |           |
    /// | raw pointers, `dyn`, params, the rest    | Unknown   |
    ///
    /// `Freeze` is shallow, so the walk goes into the type behind every reference.
    fn walk(&mut self, ty: Ty<'tcx>, behind_shared: bool) {
        if !ty.has_free_regions() || !self.seen.insert((ty, behind_shared)) {
            return;
        }
        match *ty.kind() {
            ty::Ref(region, inner, mutability) => {
                self.reference(region, inner, mutability, behind_shared);
                // A `&mut` behind a shared reference can't be written through
                self.walk(inner, behind_shared || !mutability.is_mut());
            }

            // PhantomData is considered "Token"
            ty::Adt(adt, _) if adt.is_phantom_data() => self.all(ty, OutsideKind::Token),
            // strangelove Context is considered Kernel data
            ty::Adt(adt, _) if self.tcx.is_lang_item(adt.did(), LangItem::Context) => {
                self.all(ty, OutsideKind::Kernel)
            }
            // Other abstract data types
            ty::Adt(adt, args) => {
                // A `Cell` can hand out what it holds through a shared reference
                let behind_shared = behind_shared && !adt.is_unsafe_cell();
                for field in adt.all_fields() {
                    self.walk(field.ty(self.tcx, args).skip_norm_wip(), behind_shared);
                }
            }
            ty::Tuple(tys) => {
                for ty in tys {
                    self.walk(ty, behind_shared);
                }
            }
            ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => {
                self.walk(inner, behind_shared)
            }

            // Values that hold another type. We need to label each lifetime of the outer type as
            // `Token`.
            ty::Closure(_, args) => {
                self.holds(ty, args.as_closure().tupled_upvars_ty(), behind_shared)
            }
            ty::CoroutineClosure(_, args) => {
                self.holds(ty, args.as_coroutine_closure().tupled_upvars_ty(), behind_shared)
            }
            ty::Coroutine(_, args) => {
                self.holds(ty, args.as_coroutine().tupled_upvars_ty(), behind_shared)
            }

            // A future returned from an outside fn call.
            ty::Alias(_, ty::AliasTy { kind: ty::Opaque { def_id }, args, .. })
                if let hir::OpaqueTyOrigin::FnReturn { parent, .. }
                | hir::OpaqueTyOrigin::AsyncFn { parent, .. } =
                    self.tcx.opaque_ty_origin(def_id)
                    && parent.as_local().is_none_or(|parent| {
                        self.tcx.typeck_root_def_id_local(parent) != self.root
                    }) =>
            {
                // Its fn's borrowck can shorten a lifetime to another, so `&'s Sender<'m>` can
                // become `&'s Sender<'s>`
                let hidden =
                    self.tcx.type_of_opaque(def_id).instantiate(self.tcx, args).skip_norm_wip();
                self.holds(ty, hidden, behind_shared);
            }

            // Types with a fixed kind
            ty::FnDef(..) => self.all(ty, OutsideKind::Token),
            _ => self.all(ty, OutsideKind::Unknown),
        }
    }

    /// `ty`, whose value is a `held`. The lifetimes of `ty` that `held` doesn't name point to
    /// nothing.
    fn holds(&mut self, ty: Ty<'tcx>, held: Ty<'tcx>, behind_shared: bool) {
        self.walk(held, behind_shared);
        let named = regions_in(self.tcx, self.universal_regions, held);
        for region in regions_in(self.tcx, self.universal_regions, ty) {
            if !named.contains(&region) {
                self.push(region, OutsideKind::Token, Vec::new());
            }
        }
    }

    /// The reference `&'region inner`, `behind_shared` if it is behind a shared reference
    fn reference(
        &mut self,
        region: ty::Region<'tcx>,
        inner: Ty<'tcx>,
        mutability: Mutability,
        behind_shared: bool,
    ) {
        let kind = if let ty::Adt(adt, _) = *inner.kind()
            && self.tcx.is_lang_item(adt.did(), LangItem::Context)
        {
            // The executor makes every `Context` a task sees, in its own memory
            OutsideKind::Kernel
        } else if mutability.is_mut() && !behind_shared {
            OutsideKind::Exclusive
        } else if inner.has_non_region_param() || inner.has_aliases() {
            // Can be a `Cell` of task memory
            OutsideKind::Unknown
        } else if self.tcx.erase_and_anonymize_regions(inner).is_freeze(self.tcx, self.typing_env) {
            OutsideKind::ReadOnly
        } else {
            OutsideKind::Kernel
        };
        if !region.is_bound() && !region.is_erased() {
            let inner = regions_in(self.tcx, self.universal_regions, inner);
            self.push(self.universal_regions.to_region_vid(region), kind, inner);
        }
    }

    /// Every lifetime in `ty`, all with the same memory behind them
    fn all(&mut self, ty: Ty<'tcx>, kind: OutsideKind) {
        for region in regions_in(self.tcx, self.universal_regions, ty) {
            self.push(region, kind, Vec::new());
        }
    }

    fn push(&mut self, region: RegionVid, kind: OutsideKind, inner: Vec<RegionVid>) {
        self.found.push(Used { region, kind, inner, reached: false });
    }
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
