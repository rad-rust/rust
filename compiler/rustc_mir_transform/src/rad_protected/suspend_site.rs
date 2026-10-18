use rustc_abi::VariantIdx;
use rustc_middle::mir::{
    Body, TerminatorKind, StatementKind, BasicBlock
};
use rustc_middle::ty::{CoroutineArgs, CoroutineArgsExt};


/// Where the coroutine suspends: `StateTransform`'s `discriminant(self) = state; return`
#[derive(Clone, Copy)]
pub(crate) struct SuspendSite {
    pub block: BasicBlock,
    pub state: VariantIdx,
}

/// Enumerate the suspend sites by .await()s being called
pub(crate) fn suspend_sites(body: &Body<'_>) -> Vec<SuspendSite> {
    let mut sites: Vec<SuspendSite> = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            if !matches!(data.terminator().kind, TerminatorKind::Return) {
                return None;
            }
            let StatementKind::SetDiscriminant { variant_index, .. } = data.statements.last()?.kind
            else {
                return None;
            };
            // The reserved states mark returning and panicking, not suspending.
            (variant_index.as_usize() >= CoroutineArgs::RESERVED_VARIANTS)
                .then_some(SuspendSite { block, state: variant_index })
        })
        .collect();
    sites.sort_by_key(|site| site.state);
    sites
}
