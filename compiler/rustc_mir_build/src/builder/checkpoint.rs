use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{TerminatorKind, Operand, Place, UnwindAction, CallSource, BasicBlock};
use rustc_middle::ty::TyCtxt;
use rustc_span::{sym, Span};
use rustc_hir::find_attr;

use super::Builder;

impl<'a, 'tcx> Builder<'a, 'tcx> {
    pub(super) fn inject_checkpoint_marker(&mut self, block: BasicBlock, span: Span) -> BasicBlock {
        if !Self::is_checkpoint(self.tcx, self.def_id) {
            return block;
        }

        let Some(marker_def_id) = self.tcx.get_diagnostic_item(sym::__checkpoint) else {
            return block;
        };

        let next = self.cfg.start_new_block();
        let source_info = self.source_info(span);
        let func = Operand::function_handle(self.tcx, marker_def_id, [], span);
        let destination = Place::from(self.temp(self.tcx.types.unit, span));

        self.cfg.terminate(
            block,
            source_info,
            TerminatorKind::Call {
                func,
                args: Box::new([]),
                destination,
                target: Some(next),
                unwind: UnwindAction::Continue,
                call_source: CallSource::Misc,
                fn_span: span,
            },
        );

        next
    }

    fn is_checkpoint(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
        find_attr!(tcx, def_id, RadProtected(_))
    }
}
