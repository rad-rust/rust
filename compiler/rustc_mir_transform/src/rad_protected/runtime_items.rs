use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::sym;

pub(crate) struct RuntimeItems<'tcx> {
    pub checkpoint: CheckpointFn<'tcx>,
    pub await_effects: CheckpointFn<'tcx>,
    pub restore: DefId,
    pub buffer_size: u64,
}

impl<'tcx> RuntimeItems<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Option<Self> {
        Some(Self {
            checkpoint: CheckpointFn {
                def_id: tcx.get_diagnostic_item(sym::checkpoint)?,
                name: "checkpoint".into(),
                ret_ty: tcx.types.bool,
                copy: false,
            },
            await_effects: CheckpointFn {
                def_id: tcx.get_diagnostic_item(sym::await_effects)?,
                name: "await effects".into(),
                ret_ty: tcx.types.unit,
                copy: true,
            },
            restore: tcx.get_diagnostic_item(sym::restore)?,
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

pub(crate) struct CheckpointFn<'tcx> {
    pub def_id: DefId,
    pub name: String,
    pub ret_ty: Ty<'tcx>,
    pub copy: bool,
}
