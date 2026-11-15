use rustc_middle::ty::{Ty, TyCtxt};
use rustc_hir::def_id::DefId;
use rustc_span::{sym, Span};
use rustc_abi::{Size, VariantIdx};
use rustc_attr_ir::LangItem;

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
            },
            await_effects: CheckpointFn {
                def_id: tcx.get_diagnostic_item(sym::await_effects)?,
                name: "await effects".into(),
                ret_ty: tcx.types.unit,
            },
            restore: tcx.get_diagnostic_item(sym::restore)?,
            buffer_size: get_checkpoint_buffer_size(tcx)?,
        })
    }

    pub(crate) fn poll_pending_variant(tcx: TyCtxt<'tcx>, span: Span) -> VariantIdx {
        let poll_def_id = tcx.require_lang_item(LangItem::Poll, span);
        let poll_pending_def_id = tcx.require_lang_item(LangItem::PollPending, span);
        let poll_adt_def = tcx.adt_def(poll_def_id);
        poll_adt_def.variant_index_with_id(poll_pending_def_id)
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
}
