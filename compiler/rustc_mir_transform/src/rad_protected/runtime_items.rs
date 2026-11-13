use rustc_middle::ty::TyCtxt;
use rustc_hir::def_id::DefId;
use rustc_span::sym;
use rustc_abi::Size;

pub(crate) struct RuntimeItems {
    pub checkpoint: DefId,
    pub await_effects: DefId,
    pub buffer_size: u64,
}

impl RuntimeItems {
    pub(crate) fn new<'tcx>(tcx: TyCtxt<'tcx>) -> Option<Self> {
        Some(Self {
            checkpoint: tcx.get_diagnostic_item(sym::checkpoint)?,
            await_effects: tcx.get_diagnostic_item(sym::await_effects)?,
            buffer_size: get_checkpoint_buffer_size(tcx)?,
        })
    }
}

fn get_checkpoint_buffer_size<'tcx>(tcx: TyCtxt<'tcx>) -> Option<u64> {
    let def_id = tcx.get_diagnostic_item(sym::checkpoint_buffer_size)?;

    let val = tcx.const_eval_poly(def_id).ok()?;
    let bits = val.try_to_bits(Size::from_bits(64))?;
    Some(bits as u64)
}
