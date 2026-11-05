//! Inserts the checkpoints `RadWriteSets` planned. Runs after `StateTransform`, which has turned
//! each suspension into a write of the coroutine's state followed by a return.

use rustc_data_structures::thin_vec::ThinVec;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::*;
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{CoroutineArgs, CoroutineArgsExt, Ty, TyCtxt};
use rustc_span::{Span, Spanned, sym};
use crate::PassPolicy;

use super::rad_protected::regions::Env;
use super::rad_protected::suspend_site::{SuspendSite, suspend_sites};
use super::rad_protected::logger::Logger;
use super::rad_protected::locate_stmts::Locations;

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

        let locations = Locations::resolve(&table, body);
        let sites = suspend_sites(body);

        // Make sure that the sites match the actual number of checkpoints
        assert_eq!(sites.len(), table.awaits.len(), "suspensions don't match the plan");

        for (index, (site, checkpoints)) in sites.into_iter().zip(&table.awaits).enumerate() {
            assert_eq!(site.state.as_usize(), CoroutineArgs::RESERVED_VARIANTS + index);

            let result = emit_await(tcx, body, site, checkpoints, &locations);

            if let Err(err_msg) = result {
                Logger::error(&format!("state {} skipped: {}", site.state.as_usize(), err_msg));
                break;
            };
        }

        Logger::report(tcx);
    }
}

fn emit_await<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    site: SuspendSite,
    checkpoints: &AwaitCheckpoints,
    locations: &Locations,
) -> Result<(), String> {
    let this = Env::coroutine_place(body, site.block)?;

    let checkpoint = tcx.get_diagnostic_item(sym::checkpoint).unwrap();
    let start_site = site.new_block(locations.get(checkpoints.loop_head)?.block);
    emit_checkpoint(tcx, body, start_site, this, "checkpoint", checkpoint, &checkpoints.before)?;
    
    for end in &checkpoints.ends {
        let location = locations.get(*end)?;

        split_at(tcx, body, location);

        let checkpoint = tcx.get_diagnostic_item(sym::await_effects).unwrap();
        let end_site = site.new_block(location.block);
        emit_checkpoint(tcx, body, end_site, this, "await effects", checkpoint, &checkpoints.effects)?;
    }
    Ok(())
}

fn split_at<'tcx>(_tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>, location: Location) {
    let fallback = SourceInfo::outermost(body.span);
    let blocks = body.basic_blocks_mut();
    let head = &mut blocks[location.block];
    let tail_statements = head.statements.split_off(location.statement_index);
    let old_terminator = head.terminator.take();
    let is_cleanup = head.is_cleanup;
    let source_info = old_terminator.as_ref().map_or(fallback, |t| t.source_info);

    let mut tail = BasicBlockData::new(old_terminator, is_cleanup);
    tail.statements = tail_statements;
    let tail = blocks.push(tail);

    blocks[location.block].terminator = Some(Terminator {
        source_info,
        kind: TerminatorKind::Goto { target: tail },
        loop_hint_attrs: ThinVec::new(),
        id: None,
    });
}

fn emit_checkpoint<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    site: SuspendSite,
    this: Place<'tcx>,
    which: &str,
    checkpoint: DefId,
    objects: &[(CheckpointObject, Depth)],
) -> Result<(), String> {
    let span = body.span;
    let source_info = SourceInfo::outermost(span);

    let env = Env::new(tcx, body, site, objects);
    let regions = env.get_regions(this)?;

    let n = regions.len() as u64;
    let total_bytes: u64 = regions.iter().map(|r| r.size).sum();

    Logger::info(&format!("state {} ({:?}) {which}: {n} regions, {total_bytes} bytes", site.state.as_usize(), site.block));

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
    let bool_const = |b: bool| {
        let scalar = Scalar::from_bool(b);
        Operand::const_from_scalar(tcx, tcx.types.bool, scalar, span)
    };

    // let regions: [(*mut u8, usize, bool); n];
    let u8_ptr = Ty::new_ptr(tcx, tcx.types.u8, Mutability::Mut);
    let pair_ty = Ty::new_tup(tcx, &[u8_ptr, tcx.types.usize, tcx.types.bool]);
    let array_ty = Ty::new_array(tcx, pair_ty, n);
    let array = new_local(body, array_ty);

    for (i, region) in regions.iter().enumerate() {
        // _1 = &raw mut field;
        let raw = new_local(body, Ty::new_ptr(tcx, region.ty, Mutability::Mut));
        let place = deref_region(tcx, body, span, region.place, &mut assign);
        assign(raw.into(), Rvalue::RawPtr(RawPtrKind::Mut, place));
        //  _2 = _1 as *mut u8;
        let ptr = new_local(body, u8_ptr);
        assign(ptr.into(), Rvalue::Cast(CastKind::PtrToPtr, Operand::Move(raw.into()), u8_ptr));

        // regions[i] = (_2, size, compare);
        let pair = new_local(body, pair_ty);
        let fields: IndexVec<_, _> = IndexVec::from_raw(vec![
            Operand::Move(ptr.into()),
            usize_const(region.size),
            bool_const(region.compare),
        ]);
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

fn deref_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    span: Span,
    mut place: Place<'tcx>,
    assign: &mut impl FnMut(Place<'tcx>, Rvalue<'tcx>),
) -> Place<'tcx> {
    while let Some(i) = place.projection.iter().skip(1).position(|elem| matches!(elem, PlaceElem::Deref)) {
        let i = i + 1;

        let prefix = Place { local: place.local, projection: tcx.mk_place_elems(&place.projection[..i]) };
        let ref_ty = prefix.ty(&body.local_decls, tcx).ty;

        let tmp = body.local_decls.push(LocalDecl::new(ref_ty, span));
        assign(
            tmp.into(),
            Rvalue::Use(Operand::Copy(prefix), WithRetag::No),
        );

        place = Place { local: tmp, projection: tcx.mk_place_elems(&place.projection[i..]) };
    }

    place
}
