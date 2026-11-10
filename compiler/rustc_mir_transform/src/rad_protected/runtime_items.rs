use rustc_middle::ty::TyCtxt;
use rustc_hir::def_id::DefId;
use rustc_span::sym;

pub(crate) struct RuntimeItems {
    pub checkpoint: DefId,
    pub await_effects: DefId,
}

impl RuntimeItems {
    pub(crate) fn new<'tcx>(tcx: TyCtxt<'tcx>) -> Option<Self> {
        Some(Self {
            checkpoint: tcx.get_diagnostic_item(sym::checkpoint)?,
            await_effects: tcx.get_diagnostic_item(sym::await_effects)?,
        })
    }
}
