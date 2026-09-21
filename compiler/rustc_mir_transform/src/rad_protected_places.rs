//! Place canonicalization shared by the `#[rad_protected]` MIR passes.
//!
//! The checkpoint liveness analysis and the function shadow pass both need to turn an arbitrary
//! MIR `Place` into the most precise statically identifiable, sized region that contains it. They
//! differ only in which `Deref`s they may look through; see [`DerefPolicy`].

use rustc_middle::mir::{Body, Place, PlaceRef, ProjectionElem};
use rustc_middle::ty::{TyCtxt, TypingEnv};

/// Which `Deref` projections [`canonicalize`] follows.
#[derive(Clone, Copy, PartialEq)]
pub(super) enum DerefPolicy {
    /// PR 7 behavior: follow `Deref` of any `&`/`&mut`.
    FollowRefs,
    /// Shadow behavior: follow only the leading `Deref` of the root local;
    /// stop at any later `Deref`, since the shadow does not cover pointees of T's fields.
    StopAtInnerDeref,
}

// Determines if a Place contains another Place
pub(super) trait IsPrefixOf<'tcx> {
    fn is_prefix_of(&self, other: PlaceRef<'tcx>) -> bool;
}

impl<'tcx> IsPrefixOf<'tcx> for PlaceRef<'tcx> {
    fn is_prefix_of(&self, other: PlaceRef<'tcx>) -> bool {
        self.local == other.local
            && self.projection.len() <= other.projection.len()
            && self.projection == &other.projection[..self.projection.len()]
    }
}

// Determines what is the most precise Place we can safely checkpoint (we need to
// ensure it denotes a statically identifiable, sized region suitable for checkpointing)
pub(super) fn canonicalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: TypingEnv<'tcx>,
    place: Place<'tcx>,
    policy: DerefPolicy,
) -> Option<Place<'tcx>> {
    let mut len = 0;

    for (base, elem) in place.iter_projections() {
        let follow = match elem {
            ProjectionElem::Field(..)
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::UnwrapUnsafeBinder(_)
            | ProjectionElem::ConstantIndex { from_end: false, .. } => true,

            ProjectionElem::Deref => {
                let leading_or_any = match policy {
                    DerefPolicy::FollowRefs => true,
                    DerefPolicy::StopAtInnerDeref => len == 0,
                };
                leading_or_any && base.ty(body, tcx).ty.is_ref()
            }

            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { from_end: true, .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..) => false,
        };

        if !follow {
            break;
        }

        len += 1;
    }

    let mut prefix = PlaceRef { local: place.local, projection: &place.projection[..len] };

    // Callers record `layout_of(place_ty).size` for the result, so back off to a sized prefix.
    while !prefix.ty(body, tcx).ty.is_sized(tcx, typing_env) {
        prefix = prefix.last_projection()?.0;
    }

    Some(Place { local: prefix.local, projection: tcx.mk_place_elems(prefix.projection) })
}
