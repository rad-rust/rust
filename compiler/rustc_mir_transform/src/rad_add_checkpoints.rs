//! Inserts the checkpoints `RadWriteSets` planned. Runs after `StateTransform`, which has turned
//! each suspension into a write of the coroutine's state followed by a return.

use rustc_data_structures::thin_vec::ThinVec;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::*;
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{CoroutineArgs, CoroutineArgsExt, Ty, TyCtxt};
use rustc_span::{Spanned, sym};
use crate::PassPolicy;

use super::rad_protected::regions::Env;
use super::rad_protected::suspend_site::{SuspendSite, suspend_sites};

pub(super) struct RadAddCheckpoints;

impl<'tcx> crate::MirPass<'tcx> for RadAddCheckpoints {
    fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(ctx.opts.unstable_opts.rad_write_sets)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // Taking the table keeps it out of optimized MIR and crate metadata.
        let Some(table) = body.coroutine.as_mut().and_then(|info| info.rad_checkpoints.take())
        else {
            return;
        };
        let sites = suspend_sites(body);

        // Make sure that the sites match the actual number of checkpoints
        assert_eq!(sites.len(), table.suspensions.len(), "suspensions don't match the plan");

        let checkpoint = tcx.get_diagnostic_item(sym::checkpoint).unwrap();

        let path = with_no_trimmed_paths!(tcx.def_path_str(body.source.def_id()));
        eprintln!("=== rad checkpoints: {path} ===");

        for (index, (site, objects)) in sites.into_iter().zip(&table.suspensions).enumerate() {
            assert_eq!(site.state.as_usize(), CoroutineArgs::RESERVED_VARIANTS + index);

            emit_checkpoint(tcx, body, site, checkpoint, objects).unwrap_or_else(|err| {
                eprintln!("    state {} skipped: {}", site.state.as_usize(), err)
            });
        }
    }
}

fn emit_checkpoint<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    site: SuspendSite,
    checkpoint: DefId,
    objects: &[(CheckpointObject, Depth)],
) -> Result<(), String>{
    let span = body.span;
    let source_info = SourceInfo::outermost(span);

    let env = Env::new(tcx, body, site, objects);
    let regions = env.get_regions()?;
   
    let n = regions.len() as u64;
    let total_bytes: u64 = regions.iter().map(|r| r.size).sum();
    eprintln!("  state {} ({:?}): {n} regions, {total_bytes} bytes", site.state.as_usize(), site.block);

    let mut stmts: Vec<Statement<'tcx>> = Vec::new();
    let mut assign = |place: Place<'tcx>, rvalue: Rvalue<'tcx>| {
        let kind = StatementKind::Assign(Box::new((place, rvalue)));
        stmts.push(Statement::new(source_info, kind));
    };
    let new_local = |body: &mut Body<'tcx>, ty: Ty<'tcx>| -> Local {
        body.local_decls.push(LocalDecl::new(ty, span))
    };
    let usize_const = |v: u64| {
        let scalar = Scalar::from_target_usize(v, &tcx);
        Operand::const_from_scalar(tcx, tcx.types.usize, scalar, span)
    };

    // let regions: [(*mut u8, usize); n];
    let u8_ptr = Ty::new_ptr(tcx, tcx.types.u8, Mutability::Mut);
    let pair_ty = Ty::new_tup(tcx, &[u8_ptr, tcx.types.usize]);
    let array_ty = Ty::new_array(tcx, pair_ty, n);
    let array = new_local(body, array_ty);

    for (i, region) in regions.iter().enumerate() {
        // _1 = &raw mut field; 
        let raw = new_local(body, Ty::new_ptr(tcx, region.ty, Mutability::Mut));
        assign(raw.into(), Rvalue::RawPtr(RawPtrKind::Mut, region.place));
        //  _2 = _1 as *mut u8;
        let ptr = new_local(body, u8_ptr);
        assign(ptr.into(), Rvalue::Cast(CastKind::PtrToPtr, Operand::Move(raw.into()), u8_ptr));

        // regions[i] = (_2, size);
        let pair = new_local(body, pair_ty);
        let fields: IndexVec<_, _> = IndexVec::from_raw(vec![Operand::Move(ptr.into()), usize_const(region.size)]);
        assign(pair.into(), Rvalue::Aggregate(Box::new(AggregateKind::Tuple), fields));
        let element = Place::from(array).project_deeper(
            &[ProjectionElem::ConstantIndex { offset: i as u64, min_length: n, from_end: false }],
            tcx,
        );
        assign(element, Rvalue::Use(Operand::Move(pair.into()), WithRetag::No));
    }

    // &[_; n] -> &[_]
    let array_ref = new_local(body, Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, array_ty));
    assign(array_ref.into(), Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Shared, array.into()));
    let slice_ref_ty = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, Ty::new_slice(tcx, pair_ty));
    let slice_ref = new_local(body, slice_ref_ty);
    assign(
        slice_ref.into(),
        Rvalue::Cast(
            CastKind::PointerCoercion(PointerCoercion::Unsize, CoercionSource::Implicit),
            Operand::Move(array_ref.into()),
            slice_ref_ty,
        ),
    );

    let dest = new_local(body, tcx.types.unit);
    let site_arg = Operand::const_from_scalar(
        tcx,
        tcx.types.u32,
        Scalar::from_u32(site.state.as_u32()),
        span,
    );

    let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([
        Spanned { node: site_arg, span },
        Spanned { node: Operand::Move(slice_ref.into()), span },
    ]);

    let blocks = body.basic_blocks_mut();
    let old_return = blocks[site.block].terminator.take().unwrap();
    blocks[site.block].statements.extend(stmts);
    let after = blocks.push(BasicBlockData::new(Some(old_return), false));
    blocks[site.block].terminator = Some(Terminator {
        source_info,
        kind: TerminatorKind::Call {
            func: Operand::function_handle(tcx, checkpoint, &[], span),
            args,
            destination: dest.into(),
            target: Some(after),
            unwind: UnwindAction::Continue,
            call_source: CallSource::Misc,
            fn_span: span,
        },
        loop_hint_attrs: ThinVec::new(),
        id: None,
    });

    Ok(())
}
