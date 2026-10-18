use rustc_abi::FieldIdx;
use rustc_middle::mir::{
    Body, StatementKind, PlaceElem, Place, CoroutineLayout, CheckpointObject, Depth
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_middle::ty::TypingEnv;
use super::suspend_site::SuspendSite;

pub(crate) struct Region<'tcx> {
    pub place: Place<'tcx>,
    pub ty: Ty<'tcx>,
    pub size: u64,
}

pub(crate) struct Env<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    site: SuspendSite,
    objects: &'a [(CheckpointObject, Depth)],
    typing_env: TypingEnv<'tcx>
}

impl<'tcx, 'a> Env<'tcx, 'a> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>,  site: SuspendSite, objects: &'a [(CheckpointObject, Depth)]) -> Self {
        let typing_env = body.typing_env(tcx);
        
        Self { tcx, body, site, objects, typing_env }
    }

    pub(crate) fn get_regions(&self) -> Result<Vec<Region<'tcx>>, String> {
        let StatementKind::SetDiscriminant { place: this, .. } =
            &self.body[self.site.block].statements.last().unwrap().kind
        else {
            return Err("suspend block doesn't end with SetDiscriminant".into());
        };

        let this: Place<'tcx> = **this;
        
        let ty::Coroutine(_, args) = *this.ty(&self.body.local_decls, self.tcx).ty.kind() else {
            return Err("the state is not written through a coroutine".into());
        };

        let upvar_tys: Vec<Ty<'tcx>> = args.as_coroutine().upvar_tys().iter().collect();

        let Some(layout) = self.body.coroutine.as_ref().and_then(|c| c.coroutine_layout.as_ref()) else {
            return Err("StateTransform has no coroutine layout".into());
        };

        let regions = self.regions(layout, this, &upvar_tys)?;

        Ok(regions)
    }

    fn regions(&self, layout: &CoroutineLayout<'tcx>, this: Place<'tcx>, upvar_tys: &[Ty<'tcx>]) -> Result<Vec<Region<'tcx>>, String> {
        let mut out = Vec::new();

        // TODO: Handle deep copies (Depth::Deep). Currently, depth is ignored
        for &(object, _depth) in self.objects {
            match object {
                CheckpointObject::Discriminant => {}

                CheckpointObject::Saved(field, slot) => {
                    let ty = layout.field_tys[slot].ty;
                    
                    let place = this.project_deeper(
                        &[PlaceElem::Downcast(None, self.site.state), PlaceElem::Field(field, ty)],
                        self.tcx,
                    );
                    out.push(Region { place, ty, size: self.size_of(ty)? });
                }

                CheckpointObject::Upvar(field) => {
                    let fields: Vec<usize> = match field {
                        Some(f) => vec![f.as_usize()],
                        None => (0..upvar_tys.len()).collect(),
                    };

                    for field in fields {
                        let ty = upvar_tys[field];
                        let place = this
                            .project_deeper(&[PlaceElem::Field(FieldIdx::from_usize(field), ty)], self.tcx);
                        out.push(Region { place, ty, size: self.size_of(ty)? });
                    }
                }

                CheckpointObject::Outside => {
                    // TODO: Handle CheckpointObject::Outside
                }
            }
        }

        out.retain(|r| r.size != 0);

        Ok(out)
    }

    fn size_of(&self, ty: Ty<'tcx>) -> Result<u64, String> {
        self.tcx
            .layout_of(self.typing_env.as_query_input(ty))
            .map(|layout| layout.size.bytes())
            .map_err(|_| format!("size of '{}' is unknown", ty))
    }
}
