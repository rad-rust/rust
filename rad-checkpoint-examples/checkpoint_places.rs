//! Checkpoint place-selection samples for the `#[rad_protected]` MIR analysis.
//!
//! Each function pins down one property of the place-level liveness analysis in
//! `compiler/rustc_mir_transform/src/rad_protected_liveness_analysis.rs`. The comment above each
//! one states the sync set it expects; `../../tests/rad-checkpoint-analysis/checkpoint_places.txt`
//! holds the compiler's answer, for a human to read, and the MIR dump next to it shows the address
//! and `size_of` each entry ends up using.
//!
//!     ./run-checkpoint-analysis.sh checkpoint_places.rs
//!
//! `../../tests/rad-checkpoint-analysis/test_checkpoint_places.sh` runs this same sample and makes
//! real pass/fail assertions about it (exact sync sets, exact address/`size_of` projections, no
//! parent/child duplicates, unknown/external callee handling, pointer aliasing, and checkpoint
//! placement relative to call-argument preparation and unwind edges) instead of relying on a human
//! to diff the golden file.
//!
//! `#[rad_protected]` and the `Runtime::checkpoint` it calls live in `std`, and the Rad-Rust
//! runtime only builds on Linux. `--cfg rad_no_std` therefore drives the same MIR pass without
//! `std`: it applies the internal `#[rad_protected_mir]` attribute the expansion would have added
//! and declares the `checkpoint` diagnostic item locally. The runner picks the mode automatically.
//!
//! In the `std` mode the `__guard` local that `#[rad_protected]` introduces for
//! `std::RadRustRuntime::triplicate_process()` stays live until it is dropped, so it appears in
//! every sync set, and that call is a checkpoint of its own.

#![cfg_attr(rad_no_std, no_std)]
#![cfg_attr(rad_no_std, feature(rustc_attrs))]
#![allow(dead_code, unsafe_op_in_unsafe_fn)]
#![cfg_attr(rad_no_std, allow(internal_features))]

#[cfg(rad_no_std)]
extern crate alloc;
#[cfg(rad_no_std)]
use alloc::boxed::Box;

/// Stand-in for `std::rad_protected::Runtime::checkpoint`, so that the pass finds the diagnostic
/// item it injects a call to when `std` is not available.
#[cfg(rad_no_std)]
#[rustc_diagnostic_item = "checkpoint"]
pub fn checkpoint(_entries: &[(*mut u8, usize)]) {}

// Sizes are picked so that the report makes it obvious whether a checkpoint entry used the
// projected field or the whole struct: `wanted` is 8 bytes, `Inner` is 136.
pub struct Inner {
    pub wanted: u64,
    pub unrelated: [u8; 128],
}

pub struct Outer {
    pub inner: Inner,
    pub tag: u32,
}

#[derive(Clone, Copy)]
pub struct Coordinates {
    pub x: f32,
    pub y: f32,
}

#[derive(Clone, Copy)]
pub struct Position {
    pub coordinates: Coordinates,
    pub valid: bool,
}

#[derive(Clone, Copy)]
pub struct State {
    pub id: u32,
    pub position: Position,
}

pub struct Accum {
    pub total: u64,
    pub scratch: [u8; 96],
}

/// A call, and therefore a checkpoint, that does nothing else.
#[inline(never)]
pub fn barrier() {}

/// A plain `fn(u32) -> u32`, usable as a function pointer value.
#[inline(never)]
pub fn add_one(x: u32) -> u32 {
    x + 1
}

#[inline(never)]
pub fn consume_tuple(t: (u32, u64, [u8; 64])) -> u64 {
    t.1
}

#[inline(never)]
pub fn update_position(p: &mut Position) {
    p.coordinates.x += 1.0;
    p.valid = true;
}

/// A bare local with no projection at all: the checkpoint entry is the local's own address and
/// `size_of::<u32>()`.
///
/// Expected sync set at the `barrier()` checkpoint: the temporary holding `acc` (4 bytes).
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn scalar_local(seed: u32) -> u32 {
    let acc = seed + 3;
    barrier();
    acc + 1
}

/// Two sibling fields of the same struct have to appear as two separate entries.
///
/// Expected: `(_1.0: f32)` and `(_1.1: f32)`, 4 bytes each - not one 8-byte `Coordinates`.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn sibling_fields(c: Coordinates) -> f32 {
    barrier();
    c.x + c.y
}

/// An arbitrarily deep projection through directly embedded structs.
///
/// Expected: `((_1.1: Position).0: Coordinates).0: f32`, 4 bytes - not the 12-byte `State`.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn deep_field(s: State) -> f32 {
    barrier();
    s.position.coordinates.x
}

/// The projected size, not the root local's size.
///
/// Expected: `(_1.0: Inner).0: u64` at 8 bytes. A 136-byte entry would mean the analysis fell back
/// to the whole `Inner`, and a 144-byte one that it fell back to `Outer`.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn projected_size(o: Outer) -> u64 {
    barrier();
    o.inner.wanted
}

/// A write to a whole parent kills the incoming children.
///
/// Expected: `keep` only. `s.position.coordinates.x` is read further down, but the whole-parent
/// write in between overwrites it, so it must not be live at the checkpoint. Exact set subtraction
/// would have kept it, because the set holds `s.position.coordinates.x` and the write names
/// `s.position`.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn parent_write_kills_child(mut s: State, keep: u32) -> u32 {
    barrier();
    s.position = Position { coordinates: Coordinates { x: 1.0, y: 2.0 }, valid: true };
    s.position.coordinates.x as u32 + keep
}

/// A write to one child leaves its siblings alone.
///
/// Expected: `(_1.1: f32)` only. `c.x` is overwritten before it is read again so it is dead at the
/// checkpoint, while `c.y` has to survive the write to its sibling `c.x`. Killing by root local, or
/// killing every place under the written place's *parent*, would have dropped `c.y` as well.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn child_write_keeps_sibling(mut c: Coordinates) -> f32 {
    barrier();
    c.x = 10.0;
    c.x + c.y
}

/// A parent and one of its fields both live at the same checkpoint collapse to one entry.
///
/// `t.0` is read after the barrier and the whole `t` is moved into `consume_tuple`, so both are
/// live. Expected: `_1` alone - checkpointing the parent already covers the field.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn parent_covers_child(t: (u32, u64, [u8; 64])) -> u64 {
    barrier();
    let first = t.0;
    consume_tuple(t) + first as u64
}

/// Tuple fields are projections like any other.
///
/// Expected: `(_1.0: u32)` at 4 bytes and `(_1.1: u64)` at 8 bytes. The 64-byte `t.2` is never read
/// again and must not appear.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn tuple_fields(t: (u32, u64, [u8; 64])) -> u64 {
    barrier();
    t.1 + t.0 as u64
}

/// A checkpoint inside a loop, which only terminates if the work list converges over the back edge.
///
/// Expected at the loop checkpoint: `acc.total` (8 bytes), the loop counter and `n`. The 96-byte
/// `acc.scratch` is never read and must not appear.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn loop_convergence(mut acc: Accum, n: u32) -> u64 {
    let mut i = 0u32;
    while i < n {
        barrier();
        acc.total += i as u64;
        i += 1;
    }
    acc.total
}

/// A dynamic index is not a statically known region, so the analysis falls back to the parent.
///
/// Expected: the whole `_1` array at 32 bytes, plus `i`. Reporting `_1[i]` would be a place the
/// injected MIR cannot even take the address of at a fixed offset.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn dynamic_index_read(buf: [u32; 8], i: usize) -> u32 {
    barrier();
    buf[i]
}

/// A dynamic-index *store* may land anywhere in the array, so it must not kill anything, and the
/// index it reads must still be recorded.
///
/// Expected: the whole `_1` array at 32 bytes, `i` and `v`. `i` is read *only* as the index of an
/// assignment's left-hand side, so its absence would mean the visitor dropped that read; `_1` being
/// there at all means the `buf[i] = v` store did not kill the array it cannot pin down.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn dynamic_index_store(mut buf: [u32; 8], i: usize, v: u32) -> u32 {
    barrier();
    buf[i] = v;
    buf[3]
}

/// A partially moved struct: the moved-out field must never be handed to the runtime.
///
/// Expected: `(_2.0: u64)` (`taken.wanted`) and `(_1.1: u32)` (`o.tag`). `o` as a whole is
/// partially uninitialized and must not appear.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn partial_move(mut o: Outer) -> u64 {
    let taken = o.inner;
    o.tag = 9;
    barrier();
    taken.wanted + o.tag as u64
}

/// Known gap: writes through a `&mut` parameter are observable by the caller, but plain
/// intra-procedural liveness calls them dead because nothing in this body reads them again.
///
/// Expected today: an empty sync set. Keeping `(*_1)` live to the end of the function would fix
/// this, and is deliberately left for a follow-up.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn mutable_arg(state: &mut State) {
    state.position.coordinates.x = 1.0;
    barrier();
    state.position.coordinates.y = 2.0;
    state.id = 7;
}

/// An explicit dereference of a reference is followed, so the checkpoint reads the *pointee* field
/// rather than the 8-byte pointer.
///
/// A shared reference also makes the injected MIR take a `*const` rather than a `*mut`, since a
/// `*mut` into shared memory would be an aliasing violation.
///
/// Expected: `((((*_1).1: Position).0: Coordinates).0: f32)` at 4 bytes.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn deref_field(state: &State) -> f32 {
    barrier();
    state.position.coordinates.x
}

/// Known gap: `update_position` mutates `s.position`, but nothing in this body reads it afterwards,
/// so `s.position` is not live at the `barrier()` checkpoint.
///
/// Expected: `(_1.0: u32)`, just `s.id`.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn callee_write_not_observed(mut s: State) -> u32 {
    update_position(&mut s.position);
    barrier();
    s.id
}

// ---------------------------------------------------------------------------------------------
// Additional coverage: call-prep ordering, receiver/argument rebasing, unknown callees, partial
// init via control flow, padding, aliasing, zero-sized places, recursion, and unwind edges.
// ---------------------------------------------------------------------------------------------

/// The `consume_tuple` call site is itself a checkpoint. Its sync set is the block's *out* set -
/// what the rest of the function needs afterward - which is computed independently of the
/// statements that build this very call's own arguments (`sum`). Those statements, and the call
/// itself, all move into the continuation block that runs *after* the injected checkpoint, so a
/// temporary that only this call needs must never show up in that call's own checkpoint.
///
/// Expected at the `consume_tuple(..)` checkpoint: `keep` only. `sum` is consumed entirely by the
/// call and never read again, so it must not appear even though it is computed earlier in the
/// same block.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn call_prep_temp_in_block(a: u32, keep: u32) -> u32 {
    let sum = (a as u64) + 1;
    consume_tuple((a, sum, [0u8; 64]));
    keep
}

impl Position {
    #[inline(never)]
    fn bump(&mut self) {
        self.coordinates.x += 1.0;
    }
}

/// A method call receiver rebases `&mut self` off a field projection (`s.position.bump()`
/// auto-refs to `&mut s.position`).
///
/// Expected: the `barrier()` checkpoint (the last one before the read) shows the rebased
/// projection threaded all the way through to `s.position.coordinates.x` -
/// `(((_1.1: Position).0: Coordinates).0: f32)` - not a fallback to the whole `s`. The `bump()`
/// call site is *also* a checkpoint, but every checkpoint block's own gen/kill kills everything
/// (`CheckpointAnalysis::postprocess_gen_kill`), so liveness does not flow past one checkpoint into
/// the next: `bump()`'s sync set is empty because nothing is read *between* it and the very next
/// checkpoint (`barrier()`, which has no arguments of its own). The receiver rebasing this sample
/// is named for is only externally visible in the *next* checkpoint's projection, not in an
/// inflated sync set at the call site itself.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn mut_receiver_rebase(mut s: State) -> f32 {
    s.position.bump();
    barrier();
    s.position.coordinates.x
}

#[inline(never)]
fn swap_fields(a: &mut f32, b: &mut f32) {
    let t = *a;
    *a = *b;
    *b = t;
}

/// Two `&mut` arguments taken from sibling fields of the same struct in one call. Both have to be
/// recorded as separate entries - collapsing them to their common parent would checkpoint 8 bytes
/// no differently than checkpointing each field lets the analysis tell them apart, but aliasing
/// them together, or dropping one, would be wrong.
///
/// Expected: `(_1.0: f32)` and `(_1.1: f32)` at the `barrier()` checkpoint, since it reads both
/// afterward. The `swap_fields(..)` call site is its own checkpoint too, but (as in
/// `mut_receiver_rebase`) its sync set is empty - a checkpoint's gen/kill kills everything, so
/// liveness never flows past it into the next checkpoint.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn multiple_mut_args(mut c: Coordinates) -> f32 {
    swap_fields(&mut c.x, &mut c.y);
    barrier();
    c.x + c.y
}

/// A callee reached through a function pointer has no `DefId`, so the call category the analysis
/// prints has to degrade gracefully (no `category:` line at all) instead of panicking on
/// `called_def_id`'s `None`.
///
/// Expected: the `Calls` entry for the fn-pointer call (`func: move _4 (by_value)`, no `func: const
/// ..`) has no trailing `category:` line, unlike every other entry in this file. The `barrier()`
/// checkpoint's sync set is `keep` and `r`, both read afterward; the fn-pointer call's own
/// checkpoint has an empty sync set for the same next-checkpoint-kills-everything reason as
/// `mut_receiver_rebase`.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn unknown_callee_fallback(f: fn(u32) -> u32, keep: u32) -> u32 {
    let r = f(keep);
    barrier();
    r + keep
}

/// A callee resolved to a real `DefId` in another crate (`core`) is categorized `external_crate`,
/// as opposed to the `same_crate` category every other sample in this file exercises.
///
/// Expected: the `Calls` entry for `core::hint::black_box::<u32>` reports `category:
/// external_crate`. The `barrier()` checkpoint's sync set is `r` (`_2`); `black_box`'s own
/// checkpoint is empty, again because it is immediately followed by another checkpoint.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn external_callee(keep: u32) -> u32 {
    let r = core::hint::black_box(keep);
    barrier();
    r
}

/// A local that is only conditionally assigned along one of two branches before the checkpoint -
/// definite-assignment join, rather than a single straight-line write.
///
/// Expected: `(_4: u32)` (the local holding `x`) is live at the checkpoint regardless of which
/// branch ran.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn partial_init_branch(pick: bool, a: u32, b: u32) -> u32 {
    let x;
    if pick {
        x = a;
    } else {
        x = b;
    }
    barrier();
    x
}

#[repr(C)]
pub struct Padded {
    pub flag: u8,
    pub big: u64,
}

/// `Padded` has 7 bytes of alignment padding between `flag` and `big`. The checkpoint for a
/// projected field must use that field's own size, never the padded size of the parent struct.
///
/// Expected: `(_1.1: u64)` at 8 bytes - not `_1: Padded` at 16.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn padding_struct(p: Padded) -> u64 {
    barrier();
    p.big
}

/// Two raw pointers alias the same local: `p2` is a copy of `p1`, not an independent source. The
/// pointer-alias report has to resolve `p2` back to the same root place as `p1` (`_1`, the `v`
/// argument) instead of treating it as an unrelated or unknown source.
///
/// Expected: the `Pointer/Reference aliases` section shows `_3: *mut u32 -> source _1` (`p2`
/// resolving through `p1` to `v`), i.e. no distinct/duplicate root for the aliasing pointer.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub unsafe fn aliasing_raw_ptrs(mut v: u32) -> u32 {
    let p1 = &raw mut v;
    let p2 = p1;
    barrier();
    *p2 = 9;
    v
}

pub struct WithMarker {
    pub marker: (),
    pub val: u32,
}

/// A zero-sized field sits alongside a normal one. Checkpointing it means constructing `&raw
/// (_1.0: ())` and calling `size_of::<()>()` - both well-defined for a ZST - without the analysis
/// special-casing or dropping it.
///
/// Expected: `(_1.0: ())` at 0 bytes and `(_1.1: u32)` at 4 bytes, both read after the barrier.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn zero_sized_place(w: WithMarker) -> ((), u32) {
    barrier();
    (w.marker, w.val)
}

/// A self-recursive call is a checkpoint like any other call site (`is_checkpoint` matches any
/// `Call`/`TailCall` terminator, including one whose callee is the current function). This is
/// mostly a "does not panic building the report" check: the recursive call must resolve to a
/// `same_crate` `DefId` and get a normal sync set, not special-cased or skipped.
///
/// Expected: two checkpoints. `barrier()` has sync set `[n, acc]` (`_1`, `_2`) - both are read
/// again to build the recursive call's own arguments. The recursive call's own checkpoint has sync
/// set `[_0]` - its *own return place* - because its result flows straight into `_0` and the
/// function returns it immediately after, the same "a call's own destination can be live at its own
/// checkpoint" pattern `parent_covers_child` exercises with `consume_tuple`. Its `Calls` entry
/// reports `category: same_crate`.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn recursive_checkpoint(n: u32, acc: u32) -> u32 {
    if n == 0 {
        return acc;
    }
    barrier();
    recursive_checkpoint(n - 1, acc + n)
}

pub struct Guard(pub u32);

impl Drop for Guard {
    fn drop(&mut self) {}
}

/// `g: Guard` has a `Drop` impl and is never read, only implicitly dropped - once on the normal
/// path at the end of the function, and (because it stays alive across the `consume_tuple` call)
/// again via that call's unwind (cleanup) edge to `g`'s drop glue if `consume_tuple` were to panic.
/// Unlike every other sample in this file, this one's CFG has a cleanup block.
///
/// Expected: `g` (`_1`) appears in *every* checkpoint's sync set, alongside `keep` (`_2`) - not
/// because anything reads `g`'s fields, but because `Drop::drop(&mut g)` is itself a use of `g` that
/// a successor block reaches, so liveness carries it backward like any other read. This is real:
/// the eventual drop needs `g`'s bytes intact, on both the normal-path exit and the cleanup path, so
/// checkpointing it is correct, not a false positive. It also confirms that a checkpoint block's
/// `out` set is computed from *all* of a predecessor's successors, including an unwind/cleanup
/// target, not just its normal `target`. `-Z validate-mir` (which `run-checkpoint-analysis.sh`
/// always passes) is what actually catches a malformed injection next to a cleanup edge; this
/// sample exists to keep that path exercised.
///
/// Known gap: the injected checkpoint call's own `UnwindAction` is unconditionally `Continue` (see
/// `inject_checkpoint_call`), so if the checkpoint runtime call itself were to unwind, `g` would not
/// run its destructor there. That is out of scope for this sample - the runtime call is assumed not
/// to panic - but is recorded here rather than silently relied upon.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
#[allow(unused_variables)]
pub fn unwind_edge(g: Guard, keep: u32) -> u32 {
    barrier();
    consume_tuple((keep, 0, [0u8; 64]));
    keep
}

// ---------------------------------------------------------------------------------------------
// Projections the analysis deliberately does not follow. Each of these falls back to a larger
// place; none of them may silently drop the state.
// ---------------------------------------------------------------------------------------------

pub enum Tagged {
    Small(u32),
    Large { value: u64 },
}

pub union Overlap {
    pub as_int: u32,
    pub as_float: f32,
}

pub struct Boxed {
    pub heap: Box<[u32; 4]>,
    pub tag: u8,
}

/// An enum variant is only known at run time, so the downcast is not followed.
///
/// Expected: the whole `_1: Tagged`, which covers whichever variant is active.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn enum_downcast(t: Tagged) -> u64 {
    barrier();
    match t {
        Tagged::Small(v) => v as u64,
        Tagged::Large { value } => value,
    }
}

/// Union fields overlap, so a field write cannot kill its siblings - but reading a field's bytes is
/// fine, and that is all the checkpoint does.
///
/// Expected: `(_1.0: u32)` at 4 bytes.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub unsafe fn union_field(u: Overlap) -> u32 {
    barrier();
    u.as_int
}

/// `Box` is where automatic expansion stops: the analysis checkpoints the owner, never the object
/// graph behind the pointer.
///
/// Expected: the whole `_1: Boxed`, 16 bytes - the `Box` pointer and the tag, not the 16 bytes of
/// `[u32; 4]` on the heap. (`Boxed` owns a `Box`, so it is also dropped at the end of the function,
/// which is a use of the whole local in its own right.)
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn through_box(b: Boxed) -> u32 {
    barrier();
    b.heap[0] + b.tag as u32
}

/// `*_1` is followed (it is a reference) but lands on an unsized `[u32]`, which has no
/// `size_of`, so the walk backs off to the fat pointer.
///
/// Expected: `_1: &[u32]` at 16 bytes. The elements themselves are not checkpointed.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn through_slice(s: &[u32]) -> u32 {
    barrier();
    s[0]
}

/// A raw pointer carries no validity guarantee, so its dereference is not followed.
///
/// Expected: `_1: *mut u32` at 8 bytes - the pointer value, not the pointee.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub unsafe fn through_raw_pointer(p: *mut u32) -> u32 {
    barrier();
    *p
}

/// The pass runs on generic MIR, before monomorphisation, so `size_of` stays an unevaluated
/// constant.
///
/// Expected: `(_1.1: u32)` at 4 bytes; the `T` half is never read.
#[cfg_attr(rad_no_std, rad_protected_mir)]
#[cfg_attr(not(rad_no_std), rad_protected)]
pub fn generic_tuple<T: Copy>(t: (T, u32)) -> u32 {
    barrier();
    t.1
}

#[cfg(not(rad_no_std))]
fn main() {
    assert_eq!(scalar_local(5), 9);
    assert_eq!(sibling_fields(Coordinates { x: 1.0, y: 2.0 }), 3.0);

    let state = State { id: 4, position: Position { coordinates: Coordinates { x: 5.0, y: 6.0 }, valid: false } };

    assert_eq!(deep_field(state), 5.0);
    assert_eq!(projected_size(Outer { inner: Inner { wanted: 42, unrelated: [0; 128] }, tag: 1 }), 42);
    assert_eq!(parent_write_kills_child(state, 7), 8);
    assert_eq!(child_write_keeps_sibling(Coordinates { x: 1.0, y: 2.0 }), 12.0);
    assert_eq!(parent_covers_child((1, 2, [0; 64])), 3);
    assert_eq!(tuple_fields((1, 2, [0; 64])), 3);
    assert_eq!(loop_convergence(Accum { total: 100, scratch: [0; 96] }, 3), 103);
    assert_eq!(dynamic_index_read([0, 1, 2, 3, 4, 5, 6, 7], 5), 5);
    assert_eq!(dynamic_index_store([0, 1, 2, 3, 4, 5, 6, 7], 1, 9), 3);
    assert_eq!(partial_move(Outer { inner: Inner { wanted: 42, unrelated: [0; 128] }, tag: 1 }), 51);

    let mut owned = state;
    mutable_arg(&mut owned);
    assert_eq!(owned.id, 7);
    assert_eq!(owned.position.coordinates.x, 1.0);
    assert_eq!(owned.position.coordinates.y, 2.0);

    assert_eq!(deref_field(&owned), 1.0);
    assert_eq!(callee_write_not_observed(state), 4);

    assert_eq!(call_prep_temp_in_block(2, 41), 41);
    assert_eq!(mut_receiver_rebase(state), 6.0);
    assert_eq!(multiple_mut_args(Coordinates { x: 1.0, y: 2.0 }), 3.0);
    assert_eq!(unknown_callee_fallback(add_one, 10), 21);
    assert_eq!(external_callee(42), 42);
    assert_eq!(partial_init_branch(true, 7, 9), 7);
    assert_eq!(partial_init_branch(false, 7, 9), 9);
    assert_eq!(padding_struct(Padded { flag: 1, big: 99 }), 99);
    assert_eq!(unsafe { aliasing_raw_ptrs(1) }, 9);
    assert_eq!(zero_sized_place(WithMarker { marker: (), val: 5 }), ((), 5));
    assert_eq!(recursive_checkpoint(4, 0), 10);
    assert_eq!(unwind_edge(Guard(0), 3), 3);

    assert_eq!(enum_downcast(Tagged::Large { value: 9 }), 9);
    assert_eq!(unsafe { union_field(Overlap { as_int: 3 }) }, 3);
    assert_eq!(through_box(Boxed { heap: Box::new([4, 0, 0, 0]), tag: 1 }), 5);
    assert_eq!(through_slice(&[6, 7]), 6);

    let mut cell = 8u32;
    assert_eq!(unsafe { through_raw_pointer(&raw mut cell) }, 8);
    assert_eq!(generic_tuple((1.0f64, 5)), 5);

    println!("checkpoint_places: all checks passed");
}
