use rustc_data_structures::thin_vec::ThinVec;
use rustc_middle::mir::{
    Body, BasicBlock, Local, SourceInfo, START_BLOCK, Terminator, TerminatorKind, BasicBlockData
};
use crate::rad_protected::regions::Region;

pub(crate) struct RestoreSite<'tcx> {
    pub block: BasicBlock,
    pub regions: Option<(Vec<Region<'tcx>>, Local)>,
}

pub(crate) fn generate_starting_restore_site<'tcx>(body: &mut Body<'tcx>) -> RestoreSite<'tcx> {
    let span = body.span;
    let source_info = SourceInfo::outermost(span);

    let start_block = std::mem::replace(
        &mut body.basic_blocks_mut()[START_BLOCK],
        BasicBlockData::new(None, false),
    );

    let target = body.basic_blocks_mut().push(start_block);

    body.basic_blocks_mut()[START_BLOCK].terminator = Some(Terminator {
        source_info,
        kind: TerminatorKind::Goto { target },
        loop_hint_attrs: ThinVec::new(),
        id: None,
    });

    RestoreSite { block: target, regions: None }
}
