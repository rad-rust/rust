use rustc_abi::VariantIdx;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, Local, Place, Rvalue, START_BLOCK, SourceInfo, StatementKind,
    Terminator, TerminatorKind,
};
use rustc_middle::ty::{CoroutineArgs, CoroutineArgsExt};
use rustc_span::span_bug;

use crate::rad_protected::regions::Region;
use crate::rad_protected::suspend_site::SuspendSite;

pub(crate) struct RestoreSite<'tcx> {
    pub block: BasicBlock,
    pub regions: Option<(Vec<Region<'tcx>>, Local)>,
}

/// Puts an empty block for the entry checkpoint in front of the body start and returns that block
/// and the coroutine
pub(crate) fn generate_starting_restore_site<'tcx>(
    body: &mut Body<'tcx>,
) -> (SuspendSite, Place<'tcx>) {
    // `StateTransform` starts the body with a switch on the state, whose `UNRESUMED` arm is the
    // original first block
    let start = &body.basic_blocks[START_BLOCK];
    let this = start
        .statements
        .iter()
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(assign) => match assign.1 {
                Rvalue::Discriminant(place) => Some(place),
                _ => None,
            },
            _ => None,
        })
        .unwrap_or_else(|| span_bug!(body.span, "the first block doesn't read the state"));
    let TerminatorKind::SwitchInt { targets, .. } = &start.terminator().kind else {
        span_bug!(body.span, "the first block doesn't switch on the state");
    };
    let unresumed = CoroutineArgs::UNRESUMED as u128;
    let arm =
        targets.all_values().iter().position(|&value| value.get() == unresumed).unwrap_or_else(
            || span_bug!(body.span, "the switch on the state has no `UNRESUMED` arm"),
        );
    let body_start = targets.all_targets()[arm];

    // Insert empty entry block
    let source_info = SourceInfo::outermost(body.span);
    let blocks = body.basic_blocks_mut();
    let entry = blocks.push(BasicBlockData::new(
        Some(Terminator { source_info, kind: TerminatorKind::goto(body_start), id: None }),
        false,
    ));
    let TerminatorKind::SwitchInt { targets, .. } = &mut blocks[START_BLOCK].terminator_mut().kind
    else {
        unreachable!("checked above");
    };
    targets.all_targets_mut()[arm] = entry;

    let site =
        SuspendSite { block: entry, state: VariantIdx::from_usize(CoroutineArgs::UNRESUMED) };
    (site, this)
}
