use rustc_abi::FieldIdx;
use rustc_middle::mir::{
    Body, CheckpointObject, CoroutineLayout, Depth, Place, PlaceElem, StatementKind,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TypingEnv};
use rustc_middle::ty::consts::ConstExt;
use super::suspend_site::SuspendSite;
use super::logger::Logger;

pub(crate) struct Region<'tcx> {
    pub place: Place<'tcx>,
    pub ty: Ty<'tcx>,
    pub size: u64,
    pub compare: bool,
}

pub(crate) struct Env<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    site: SuspendSite,
    objects: &'a [(CheckpointObject, Depth)],
    typing_env: TypingEnv<'tcx>,

    head_ty: Option<Ty<'tcx>>,
    regions: Vec<Region<'tcx>>,
}

const MAX_UNROLL: u64 = 16;
const MAX_DEPTH: u8 = 6;

const SKIP_CHECKPOINT_MSG: &'static str = "the data it points to will not be checkpointed";

impl<'tcx, 'a> Env<'tcx, 'a> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, site: SuspendSite, objects: &'a [(CheckpointObject, Depth)]) -> Self {
        let typing_env = body.typing_env(tcx);

        Self { tcx, body, site, objects, typing_env, head_ty: None, regions: vec![] }
    }

    pub(crate) fn get_regions(mut self) -> Result<Vec<Region<'tcx>>, String> {
        let body = self.body;

        let Some(StatementKind::SetDiscriminant { place: this, .. }) =
            body[self.site.block].statements.last().map(|statement| &statement.kind)
        else {
            return Err("suspend block doesn't end with SetDiscriminant".into());
        };

        let this: Place<'tcx> = **this;

        let ty::Coroutine(_, args) = *this.ty(&body.local_decls, self.tcx).ty.kind() else {
            return Err("the state is not written through a coroutine".into());
        };

        let upvar_tys: Vec<Ty<'tcx>> = args.as_coroutine().upvar_tys().iter().collect();

        let Some(layout) = body.coroutine.as_ref().and_then(|c| c.coroutine_layout.as_ref()) else {
            return Err("StateTransform left no coroutine layout".into());
        };

        self.collect_regions(layout, this, &upvar_tys);

        Ok(self.regions)
    }

    fn collect_regions(&mut self, layout: &CoroutineLayout<'tcx>, this: Place<'tcx>, upvar_tys: &[Ty<'tcx>]) {
        let objects = self.objects;

        for &(object, object_depth) in objects {
            let deep = object_depth == Depth::Deep;

            match object {
                CheckpointObject::Discriminant => {},

                CheckpointObject::Saved(field, slot) => {
                    let ty = layout.field_tys[slot].ty;
                    self.head_ty = Some(ty);
                    
                    let place = this.project_deeper(
                        &[PlaceElem::Downcast(None, self.site.state), PlaceElem::Field(field, ty)],
                        self.tcx,
                    );
                    self.regions(place, ty, deep, 0);
                },

                CheckpointObject::Upvar(field) => {
                    let fields: Vec<usize> = match field {
                        Some(f) => vec![f.as_usize()],
                        None => (0..upvar_tys.len()).collect(),
                    };

                    for field in fields {
                        let ty = upvar_tys[field];
                        self.head_ty = Some(ty);
                        self.field(this, field, ty, deep, 0);
                    }
                },
                
                CheckpointObject::Outside => {},
            }
        }
    }

    fn regions(&mut self, place: Place<'tcx>, ty: Ty<'tcx>, deep: bool, depth: u8) {
        let ty = self.norm(ty);
        let size = 
            match self.size_of(ty) {
                Err(err) => {
                    self.warn(ty, &err);
                    return;
                }
                Ok(0) => { return; },
                Ok(s) => s,
            };
            
        match *ty.kind() {

            // Primitive datatypes, treat as opaque data
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::FnPtr(..) | ty::Pat(..) => {
                self.opaque(place, ty, size, true);
            }

            // Unsized, size of 0, or no layout: early exit above
            ty::Str | ty::Slice(_) | ty::Dynamic(..) | ty::Foreign(_) | ty::Never | ty::FnDef(..) |
            ty::Alias(..) | ty::Param(_) | ty::Bound(..) | ty::Placeholder(..) | ty::Infer(..) | ty::Error(_) => {
                unreachable!()
            }

            // Opaque, always a ptr
            ty::RawPtr(..) => {
                self.opaque_ptr(place, ty, size);
            }

            ty::Adt(adt_def, args) => {
                match adt_def.adt_kind() {
                    ty::AdtKind::Struct => {
                        for (i, field) in adt_def.all_fields().enumerate() {
                            let field_ty = field.ty(self.tcx, args).skip_normalization();
                            self.field(place, i, field_ty, deep, depth);
                        }
                    }
                    // Opaque with possibility for pointer
                    ty::AdtKind::Union | ty::AdtKind::Enum => {
                        self.opaque_maybe_ptr(place, ty, size);
                    }
                }
            }

            ty::Tuple(tys) => {
                for (i, field_ty) in tys.iter().enumerate() {
                    self.field(place, i, field_ty, deep, depth);
                }
            }

            ty::Array(elem, len) => {
                match len.try_to_target_usize(self.tcx) {
                    
                    _ if self.is_primitive(elem) => self.opaque(place, ty, size, true),
                    Some(count) if count <= MAX_UNROLL => {
                        for offset in 0..count {
                            let element = place.project_deeper(
                                &[PlaceElem::ConstantIndex { offset, min_length: count, from_end: false }],
                                self.tcx,
                            );
                            self.regions(element, elem, deep, depth);
                        }
                    }
                    _ => self.opaque_maybe_ptr(place, ty, size),
                }
            }

            ty::Ref(_, pointee, _) => {
                self.opaque(place, ty, size, false);

                if !deep {
                    return;
                }

                if depth >= MAX_DEPTH {
                    self.warn(ty, &format!("exceeds {MAX_DEPTH} nested references: {SKIP_CHECKPOINT_MSG}"));
                    return;
                }

                if !pointee.is_sized(self.tcx, self.typing_env) {
                    self.warn(ty, &format!("points to unsized data: {SKIP_CHECKPOINT_MSG}"));
                    return;
                }

                let target = place.project_deeper(&[PlaceElem::Deref], self.tcx);
                self.regions(target, pointee, true, depth + 1);
            }

            // Opaque that might contain a ptr
            ty::UnsafeBinder(_) | ty::Closure(..) | ty::CoroutineClosure(..) | ty::Coroutine(..) | ty::CoroutineWitness(..) => {
                self.opaque_maybe_ptr(place, ty, size);
            }
        }
    }

    fn opaque(&mut self, place: Place<'tcx>, ty: Ty<'tcx>, size: u64, compare: bool) {
        self.regions.push(Region { place, ty, size, compare })
    }

    fn opaque_ptr(&mut self, place: Place<'tcx>, ty: Ty<'tcx>, size: u64) {
        self.error(ty, &format!("holds a pointer: {SKIP_CHECKPOINT_MSG}"));
        self.opaque(place, ty, size, false);
    }

    fn opaque_maybe_ptr(&mut self, place: Place<'tcx>, ty: Ty<'tcx>, size: u64) {
        self.warn(ty, &format!("may hold a pointer: {SKIP_CHECKPOINT_MSG}"));
        self.opaque(place, ty, size, false);
    }

    fn warn(&self, ty: Ty<'tcx>, message: &str) {
        self.report(ty, message, false);
    }

    fn error(&self, ty: Ty<'tcx>, message: &str) {
        self.report(ty, message, true);
    }

    fn report(&self, ty: Ty<'tcx>, message: &str, error: bool) {
        let message = match self.head_ty {
            Some(head) if self.norm(head) != ty => {
                format!("'{ty}' within '{head}' {message}")
            },
            _ => format!("'{ty}' {message}"),
        };

        if error {
            Logger::error(&message);
        } else {
            Logger::warn(&message);
        }
    }

    fn is_primitive(&self, ty: Ty<'tcx>) -> bool {
        matches!(
            ty.kind(),
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::FnPtr(..) | ty::Pat(..)
        )
    }

    fn field(&mut self, place: Place<'tcx>, i: usize, ty: Ty<'tcx>, deep: bool, depth: u8) {
        let ty = self.norm(ty);

        let place =
            place.project_deeper(&[PlaceElem::Field(FieldIdx::from_usize(i), ty)], self.tcx);

        self.regions(place, ty, deep, depth)
    }

    fn norm(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.tcx.normalize_erasing_regions(
            self.typing_env,
            ty::Unnormalized::new(ty),
        )
    }

    fn size_of(&self, ty: Ty<'tcx>) -> Result<u64, String> {
        self.tcx
            .layout_of(self.typing_env.as_query_input(ty))
            .map(|layout| layout.size.bytes())
            .map_err(|_| format!("size of '{ty}' is unknown"))
    }
}
