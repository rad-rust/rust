use either::Either;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self as hir, BlockCheckMode, HeaderSafety, Safety, UnsafeSource};
use rustc_middle::hir::nested_filter;
use rustc_middle::mir::{Body, Location, StatementId, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::PassPolicy;
use crate::diagnostics::RadUnsafe;

/// Numbers every statement and terminator before borrowck clones the body, so borrowck's
/// results can be attached to exactly the same instructions in later MIR.
pub(super) struct RadStatementIds;

impl<'tcx> crate::MirPass<'tcx> for RadStatementIds {
    fn policy(&self, _ctx: &crate::PassCtx<'_>) -> PassPolicy {
        // Bodies without `#[rad::checkpoint]` are skipped in `run_pass`
        PassPolicy::optional(true)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Only bodies marked `#[rad::checkpoint]` are analyzed.
        let def_id = body.source.def_id();
        if !tcx.rad_checkpointed(def_id) {
            return;
        }

        // Make sure that none of the marked fns have `unsafe`.
        if let Some(local) = def_id.as_local()
            && !tcx.is_typeck_child(def_id)
        {
            let item = tcx.def_span(local);
            if let Some(sig) = tcx.hir_fn_sig_by_hir_id(tcx.local_def_id_to_hir_id(local))
                && let HeaderSafety::Normal(Safety::Unsafe) = sig.header.safety
            {
                tcx.dcx().emit_err(RadUnsafe { span: sig.span, item: None });
            }
            if let Some(hir_body) = tcx.hir_maybe_body_owned_by(local) {
                UnsafeBlocks { tcx, item }.visit_body(hir_body);
            }
        }

        let mut ids = (0..).map(StatementId::from_usize);
        for data in body.basic_blocks.as_mut_preserves_cfg() {
            for statement in &mut data.statements {
                statement.id = ids.next();
            }
            data.terminator_mut().id = ids.next();
        }
    }
}

/// Finds the `unsafe` blocks the user wrote in a body
struct UnsafeBlocks<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// The marked fn, for the error's label
    item: Span,
}

impl<'tcx> Visitor<'tcx> for UnsafeBlocks<'tcx> {
    // Closures and `async` blocks are nested bodies of the fn; nested items are other functions
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_block(&mut self, block: &'tcx hir::Block<'tcx>) {
        // Skip blocks the compiler made and `unsafe` that comes from `#[allow_internal_unsafe]`
        // or from another crate's macro (such as `pin!`).
        if let BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided) = block.rules
            && !block.span.allows_unsafe()
            && !block.span.in_external_macro(self.tcx.sess.source_map())
        {
            self.tcx.dcx().emit_err(RadUnsafe { span: block.span, item: Some(self.item) });
        }
        intravisit::walk_block(self, block);
    }
}

/// The id of the statement or terminator at `location`.
pub(super) fn id_at(body: &Body<'_>, location: Location) -> Option<StatementId> {
    match body.stmt_at(location) {
        Either::Left(statement) => statement.id,
        Either::Right(terminator) => terminator.id,
    }
}

/// The id of the statement or terminator at `location`, as printed.
pub(super) fn id_label(body: &Body<'_>, location: Location) -> String {
    id_at(body, location).map_or_else(|| "-".to_string(), |id| format!("{id:?}"))
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
