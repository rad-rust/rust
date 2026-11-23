use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::sym;

pub(crate) struct RuntimeItems<'tcx> {
    pub checkpoint: RegionsFn<'tcx>,
    pub await_effects: RegionsFn<'tcx>,
    pub restore: DefId,
    pub bad_state: DefId,
    pub buffer_size: u64,
}

impl<'tcx> RuntimeItems<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Option<Self> {
        Some(Self {
            checkpoint: RegionsFn {
                def_id: tcx.get_diagnostic_item(sym::checkpoint)?,
                name: "checkpoint".into(),
                ret_ty: tcx.types.bool,
            },
            await_effects: RegionsFn {
                def_id: tcx.get_diagnostic_item(sym::await_effects)?,
                name: "await effects".into(),
                ret_ty: tcx.types.unit,
            },
            restore: tcx.get_diagnostic_item(sym::restore)?,
            bad_state: tcx.get_diagnostic_item(sym::bad_state)?,
            buffer_size: get_checkpoint_buffer_size(tcx)?,
        })
    }
}

fn get_checkpoint_buffer_size<'tcx>(tcx: TyCtxt<'tcx>) -> Option<u64> {
    let def_id = tcx.get_diagnostic_item(sym::checkpoint_buffer_size)?;

    let val = tcx.const_eval_poly(def_id).ok()?;
    let pointer_size = tcx.data_layout.pointer_size();
    let bits = val.try_to_bits(pointer_size)?;

    Some(bits as u64)
}

pub(crate) struct RegionsFn<'tcx> {
    pub def_id: DefId,
    pub name: String,
    pub ret_ty: Ty<'tcx>,
}
