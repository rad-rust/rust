//! Inserts the plan `RadWriteSets` planned. Runs after `StateTransform`, which has turned
//! each suspension into a write of the coroutine's state followed by a return.

use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::thin_vec::ThinVec;
use rustc_index::IndexVec;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::*;
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{CoroutineArgs, CoroutineArgsExt, Ty, TyCtxt};
use rustc_span::{Span, Spanned};

use super::rad_protected::locate_stmts::{Locations, ResolvedLocations};
use super::rad_protected::logger::Logger;
use super::rad_protected::regions::Env;
use super::rad_protected::runtime_items::{RegionsFn, RuntimeItems};
use super::rad_protected::suspend_site::{SuspendSite, suspend_sites};
use crate::PassPolicy;
use crate::rad_protected::regions::Region;
use crate::rad_protected::restore_site::generate_starting_restore_site;

pub(super) struct RadAddCheckpoints;

impl<'tcx> crate::MirPass<'tcx> for RadAddCheckpoints {
    fn policy(&self, _ctx: &crate::PassCtx<'_>) -> PassPolicy {
        // Bodies without `#[rad::checkpoint]` are skipped in `run_pass`
        PassPolicy::optional(true)
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let Some(runtime) = RuntimeItems::new(tcx) else {
            return;
        };

        // Taking the table keeps it out of optimized MIR and crate metadata.
        let Some(table) = body.coroutine.as_mut().and_then(|info| info.rad_checkpoints.take())
        else {
            return;
        };

        // Group entries by the ending `.await`
        let mut groups: Vec<Vec<_>> = Vec::new();
        for (&(from, to), plan) in &table.intervals {
            let to = match to {
                IntervalEnd::Await(to) => to,
                // TODO: Emit the compare and rollback before the return
                IntervalEnd::Return => continue,
            };
            if groups.len() <= to {
                groups.resize_with(to + 1, Vec::new);
            }
            groups[to].push((from, plan));
        }
        let Some(firsts) = groups
            .iter()
            .map(|group| group.first().map(|&(_, plan)| plan))
            .collect::<Option<Vec<_>>>()
        else {
            Logger::error("an `.await` has no interval in the checkpoint table");
            return;
        };

        let locations = match Locations::resolve(&firsts, body) {
            Ok(l) => l,
            Err(err_msg) => {
                Logger::error(&format!("Failed to resolve locations: {err_msg}"));
                return;
            }
        };

        let sites = suspend_sites(body);

        // Make sure that the sites match the actual number of plan
        assert_eq!(sites.len(), groups.len(), "suspensions don't match the plan");

        let entry = match emit_entry(tcx, body, &runtime, &table.entry) {
            Ok(s) => s,
            Err(err_msg) => {
                Logger::error(&format!("entry skipped: {err_msg}"));
                Logger::report(tcx);
                return;
            }
        };

        // Populate restore_sites with the entry and end of each `.await`
        let mut restore_sites = vec![entry];
        for (index, (&site, group)) in sites.iter().zip(&groups).enumerate() {
            assert_eq!(site.state.as_usize(), CoroutineArgs::RESERVED_VARIANTS + index);

            let result: Result<BasicBlock, String> = try {
                let this = Env::coroutine_place(body, site.block)?;
                let &(_, plan) =
                    group.first().ok_or_else(|| "no interval ends at this `.await`".to_string())?;
                let agree = group.iter().all(|(_, other)| {
                    other.effects == plan.effects
                        && other.loop_head == plan.loop_head
                        && other.ends == plan.ends
                });
                if !agree {
                    Err(String::from(
                        "the intervals of this `.await` disagree on `effects`, `loop_head` or `ends`",
                    ))?;
                }

                // TODO: We assume there's only a single restore point, which may not always be true
                let ends = &locations.get(index).ends;
                assert_eq!(ends.len(), 1);
                let end = ends.last().unwrap();
                split_at(tcx, body, end);

                let end_site = site.new_block(end.block);
                emit_restore_site(tcx, body, end_site, this, &runtime, &plan.effects)?
            };

            match result {
                Ok(s) => restore_sites.push(s),
                Err(err_msg) => {
                    Logger::error(&format!("state {} skipped: {}", site.state.as_usize(), err_msg));
                    Logger::report(tcx);
                    return;
                }
            }
        }

        // Build checkpoint and restore sites for each of the awaits we just built in restore_sites
        for (index, (site, group)) in sites.into_iter().zip(&groups).enumerate() {
            let locations = locations.get(index);
            let result = emit_await(tcx, body, site, group, locations, &runtime, &restore_sites);

            if let Err(err_msg) = result {
                Logger::error(&format!("state {} skipped: {}", site.state.as_usize(), err_msg));
                break;
            }
        }

        Logger::report(tcx);
    }
}

/// Emit a checkpoint when the function starts.
fn emit_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    runtime: &RuntimeItems<'tcx>,
    objects: &[(CheckpointObject, Depth)],
) -> Result<BasicBlock, String> {
    let (site, this) = generate_starting_restore_site(body);
    if objects.is_empty() {
        // A rollback to the function entry has nothing to restore when the function has no args
        return Ok(site.block);
    }
    emit_restore_site(tcx, body, site, this, runtime, objects)
}

/// Emit the checkpoint and rollback of an `.await`. Since an `.await` can be reached from multiple
/// earlier `.await`s, we create unique rollbacks for each interval and pick the branch by the
/// coroutine state that the last restore site wrote.
///
/// Before:
///
///     head: ...; goto -> poll loop
///
/// After, for an `.await` whose intervals start at A and B:
///
///     head: ...; _d = discriminant(this); switchInt(copy _d)
///       |-- state(A) --> ok = checkpoint(site, writes(A -> site)) --+
///       |-- state(B) --> ok = checkpoint(site, writes(B -> site)) --+
///       '-- otherwise -> bad_state(site)                            |
///                                                                   v
///     join: switchInt(move ok)
///       |-- true ---> accepted: goto -> poll loop
///       '-- false --> rollback: switchInt(move _d)
///                       |-- state(A) --> restore(state(A), future, size) --> restore site A
///                       |-- state(B) --> restore(state(B), future, size) --> restore site B
///                       '-- otherwise -> bad_state(site)
fn emit_await<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    site: SuspendSite,
    group: &[(IntervalStart, &AwaitCheckpoints)],
    locations: &ResolvedLocations,
    runtime: &RuntimeItems<'tcx>,
    restore_sites: &[BasicBlock],
) -> Result<(), String> {
    let this = Env::coroutine_place(body, site.block)?;

    let span = body.span;
    let source_info = SourceInfo::outermost(span);
    let goto = |target| Terminator {
        source_info,
        kind: TerminatorKind::Goto { target, loop_hint_attrs: ThinVec::new() },
        id: None,
    };

    // Move the jump into the poll loop to its own block, so that every interval's handler can end there
    let head = locations.loop_head.unwrap().block;
    let blocks = body.basic_blocks_mut();
    let into_loop = blocks[head].terminator.take().unwrap();
    let join = blocks.push(BasicBlockData::new(Some(into_loop), false));
    let ok = body.local_decls.push(LocalDecl::new(tcx.types.bool, span));

    // Throw an error when no interval of this `.await` starts at the current state
    let site_arg =
        Operand::const_from_scalar(tcx, tcx.types.u32, Scalar::from_u32(site.state.as_u32()), span);
    let never = body.local_decls.push(LocalDecl::new(tcx.types.never, span));
    let bad_state = body.basic_blocks_mut().push(BasicBlockData::new(
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Call {
                func: Operand::function_handle(tcx, runtime.bad_state, &[], span),
                args: Box::new([Spanned { node: site_arg, span }]),
                destination: never.into(),
                target: None,
                unwind: UnwindAction::Continue,
                call_source: CallSource::Misc,
                fn_span: span,
            },
            id: None,
        }),
        false,
    ));

    // Pick the interval that ran by the state its restore site wrote
    let mut compares = Vec::new();
    let mut intervals = Vec::new();
    for &(from, plan) in group {
        let arm = body.basic_blocks_mut().push(BasicBlockData::new(Some(goto(join)), false));
        // Emit the compare checkpoint that sends this interval's writes to the other core
        let compare_call = emit_regions_call(
            tcx,
            body,
            site.new_block(arm),
            this,
            &runtime.checkpoint,
            &plan.interval_writes,
        )?;
        validate_payload_size(runtime.buffer_size, compare_call.total_bytes)?;

        let verdict = Rvalue::Use(Operand::Move(compare_call.dest.into()), WithRetag::No);
        let verdict = StatementKind::Assign(Box::new((ok.into(), verdict)));
        body.basic_blocks_mut()[compare_call.target]
            .statements
            .insert(0, Statement::new(source_info, verdict));

        compares.push((from.state().as_u32().into(), arm));
        intervals.push(from);
    }

    // Read the state once, so that the rollback picks the same interval as the compare
    let discr_ty = this.ty(&body.local_decls, tcx).ty.discriminant_ty(tcx);
    let discr = body.local_decls.push(LocalDecl::new(discr_ty, span));
    let read = StatementKind::Assign(Box::new((discr.into(), Rvalue::Discriminant(this))));
    let blocks = body.basic_blocks_mut();
    blocks[head].statements.push(Statement::new(source_info, read));
    blocks[head].terminator = Some(Terminator {
        source_info,
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Copy(discr.into()),
            targets: SwitchTargets::new(compares.into_iter(), bad_state),
        },
        id: None,
    });

    // Make the rollback block with the runtime call including the entire future
    let mut rollbacks = Vec::new();
    for from in intervals {
        let state = from.state();
        let restore_site = match from {
            IntervalStart::Entry => restore_sites[0],
            IntervalStart::Await(index) => restore_sites[index + 1],
        };

        let state_arg =
            Operand::const_from_scalar(tcx, tcx.types.u32, Scalar::from_u32(state.as_u32()), span);

        // Pass the address of the future, which is only known when the task runs
        let future_ty = this.ty(&body.local_decls, tcx).ty;
        let u8_ptr = Ty::new_ptr(tcx, tcx.types.u8, Mutability::Mut);
        let raw = body.local_decls.push(LocalDecl::new(Ty::new_mut_ptr(tcx, future_ty), span));
        let future = body.local_decls.push(LocalDecl::new(u8_ptr, span));
        let take_raw = Rvalue::RawPtr(RawPtrKind::Mut, this);
        let cast = Rvalue::Cast(CastKind::PtrToPtr, Operand::Move(raw.into()), u8_ptr);
        let stmts = vec![
            Statement::new(source_info, StatementKind::Assign(Box::new((raw.into(), take_raw)))),
            Statement::new(source_info, StatementKind::Assign(Box::new((future.into(), cast)))),
        ];

        // Leave the size to codegen, since the layout of the future depends on this body
        let size_of = tcx.require_lang_item(LangItem::SizeOf, span);
        let size = Operand::unevaluated_constant(tcx, size_of, &[future_ty.into()], span);

        let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([
            Spanned { node: state_arg, span },
            Spanned { node: Operand::Move(future.into()), span },
            Spanned { node: size, span },
        ]);

        // Emit the restore that puts back the committed bytes, then jump to the restore site
        let dest = body.local_decls.push(LocalDecl::new(tcx.types.unit, span));
        let arm = body.basic_blocks_mut().push(BasicBlockData::new_stmts(
            stmts,
            Some(Terminator {
                source_info,
                kind: TerminatorKind::Call {
                    func: Operand::function_handle(tcx, runtime.restore, &[], span),
                    args,
                    destination: dest.into(),
                    target: Some(restore_site),
                    unwind: UnwindAction::Continue,
                    call_source: CallSource::Misc,
                    fn_span: span,
                },
                id: None,
            }),
            false,
        ));
        rollbacks.push((state.as_u32().into(), arm));
    }

    // Add the rollback block to the MIR body
    let rollback = body.basic_blocks_mut().push(BasicBlockData::new(
        Some(Terminator {
            source_info,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Move(discr.into()),
                targets: SwitchTargets::new(rollbacks.into_iter(), bad_state),
            },
            id: None,
        }),
        false,
    ));

    // Change the join block to either roll back when the other core rejects the interval, or go on into the poll loop otherwise
    let blocks = body.basic_blocks_mut();
    let into_loop = blocks[join].terminator.take().unwrap();
    let accepted = blocks.push(BasicBlockData::new(Some(into_loop), false));
    blocks[join].terminator = Some(Terminator {
        source_info,
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Move(ok.into()),
            targets: SwitchTargets::new([(0, rollback)].into_iter(), accepted),
        },
        id: None,
    });
    Ok(())
}

/// Emit a checkpoint for the side effects of an await and return the site restored by a later rollback.
fn emit_restore_site<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    site: SuspendSite,
    this: Place<'tcx>,
    runtime: &RuntimeItems<'tcx>,
    objects: &[(CheckpointObject, Depth)],
) -> Result<BasicBlock, String> {
    let commit_call = emit_regions_call(tcx, body, site, this, &runtime.await_effects, objects)?;
    validate_payload_size(runtime.buffer_size, commit_call.total_bytes)?;

    // Mark this site as the last one that ran, even when the `.await` did not suspend
    let mark = StatementKind::SetDiscriminant { place: Box::new(this), variant_index: site.state };
    let source_info = SourceInfo::outermost(body.span);
    body.basic_blocks_mut()[commit_call.target]
        .statements
        .insert(0, Statement::new(source_info, mark));
    Ok(commit_call.target)
}

fn split_at<'tcx>(_tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>, location: &Location) {
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
        kind: TerminatorKind::Goto { target: tail, loop_hint_attrs: ThinVec::new() },
        id: None,
    });
}

struct RegionsCall {
    target: BasicBlock,
    dest: Local,
    total_bytes: u64,
}

fn emit_regions_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    site: SuspendSite,
    this: Place<'tcx>,
    func: &RegionsFn<'tcx>,
    objects: &[(CheckpointObject, Depth)],
) -> Result<RegionsCall, String> {
    let span = body.span;
    let source_info = SourceInfo::outermost(span);

    let env = Env::new(tcx, body, site, objects);
    let regions = env.get_regions(this)?;

    let n = regions.len() as u64;
    let total_bytes: u64 = regions.iter().map(|r| r.size).sum();

    Logger::info(&format!(
        "state {} ({:?}) {}: {n} regions, {total_bytes} bytes",
        site.state.as_usize(),
        site.block,
        func.name
    ));

    let (slice_ref, stmts) = build_regions(tcx, body, &regions);

    let dest = body.local_decls.push(LocalDecl::new(func.ret_ty, span));
    let site_arg =
        Operand::const_from_scalar(tcx, tcx.types.u32, Scalar::from_u32(site.state.as_u32()), span);

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
            func: Operand::function_handle(tcx, func.def_id, &[], span),
            args,
            destination: dest.into(),
            target: Some(after),
            unwind: UnwindAction::Continue,
            call_source: CallSource::Misc,
            fn_span: span,
        },
        id: None,
    });

    Ok(RegionsCall { target: after, dest, total_bytes })
}

fn build_regions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    regions: &Vec<Region<'tcx>>,
) -> (Local, Vec<Statement<'tcx>>) {
    let span = body.span;
    let source_info = SourceInfo::outermost(span);
    let n = regions.len() as u64;

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
    assign(
        array_ref.into(),
        Rvalue::Ref(tcx.lifetimes.re_erased, BorrowKind::Shared, array.into()),
    );
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

    (slice_ref, stmts)
}

fn deref_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    span: Span,
    mut place: Place<'tcx>,
    assign: &mut impl FnMut(Place<'tcx>, Rvalue<'tcx>),
) -> Place<'tcx> {
    while let Some(i) =
        place.projection.iter().skip(1).position(|elem| matches!(elem, PlaceElem::Deref))
    {
        let i = i + 1;

        let prefix =
            Place { local: place.local, projection: tcx.mk_place_elems(&place.projection[..i]) };
        let ref_ty = prefix.ty(&body.local_decls, tcx).ty;

        let tmp = body.local_decls.push(LocalDecl::new(ref_ty, span));
        assign(tmp.into(), Rvalue::Use(Operand::Copy(prefix), WithRetag::No));

        place = Place { local: tmp, projection: tcx.mk_place_elems(&place.projection[i..]) };
    }

    place
}

fn validate_payload_size(buffer_size: u64, total_bytes: u64) -> Result<(), String> {
    if total_bytes > buffer_size {
        return Err(format!(
            "Payload size of {} exceeds checkpoint buffer size of {}",
            total_bytes, buffer_size
        ));
    }
    Ok(())
}
