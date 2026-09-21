//! Samples for the `#[rad_protected(shadow_only)]` function-level shadow MIR pass
//! (`compiler/rustc_mir_transform/src/rad_protected_function_shadow.rs`).
//!
//! Each function pins down one property of the transformation: which argument gets shadowed, which
//! projections end up in the copy-in set (everything the body uses) and in the compile-time
//! may-dirty commit set (everything it may write), and which bodies are left alone. The comment
//! above each one states what it expects; the pass writes its answer to stderr, together with
//! `copied N of M bytes`, and the MIR dump next to it shows the per-place copy-in, the argument
//! rebinding and the commit statements.
//!
//! Every shadowed function is declared through `shadowed!`, which also emits an unprotected twin
//! with the very same body. `run_checks` runs both on the same inputs and requires the caller's
//! state and the return value to match.
//!
//!     ./run-checkpoint-analysis.sh function_shadow.rs
//!
//! `../../tests/rad-shadow-analysis/test_function_shadow.sh` runs this same sample, makes real
//! pass/fail assertions about the report and the dumped MIR, and then builds and runs it so the
//! runtime behaviour is checked too.
//!
//! `shadow_only` injects no runtime calls at all - no `triplicate_process()`, no `checkpoint(...)`
//! - so this sample builds and runs with or without the Linux-only Rad-Rust runtime. Without
//! `std`, `--cfg rad_no_std` swaps `fn main` for a `#[no_mangle] extern "C"` one and reports
//! through `write(2)`. This fork rewrites every `unsafe` *block* into a `std::RadRustRuntime`
//! critical section, so the `no_std` half reaches libc from `unsafe fn` bodies instead.

#![cfg_attr(rad_no_std, no_std)]
#![cfg_attr(rad_no_std, no_main)]
#![allow(dead_code, unsafe_op_in_unsafe_fn)]

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Position {
    pub x: u32,
    pub y: u32,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct State {
    pub position: Position,
    pub counter: u32,
    pub samples: [u32; 4],
}

/// A state that is not `Copy`, because it has a `Drop` impl.
pub struct Owned {
    pub counter: u32,
}

impl Drop for Owned {
    fn drop(&mut self) {}
}

/// A `Copy` state that still reaches memory the shadow copy does not own.
#[derive(Clone, Copy)]
pub struct WithPtr {
    pub counter: u32,
    pub elsewhere: *mut u32,
}

/// The pointer is a field of a field, so finding it means recursing through ADT fields rather than
/// only looking at the type's own generic arguments.
#[derive(Clone, Copy)]
pub struct Nested {
    pub inner: WithPtr,
}

/// A shared reference inside the state, which cannot be written through.
#[derive(Clone, Copy)]
pub struct WithShared<'a> {
    pub counter: u32,
    pub label: &'a u32,
}

/// A shared reference to interior-mutable memory: writable without a `&mut`.
#[derive(Clone, Copy)]
pub struct WithCell<'a> {
    pub counter: u32,
    pub external: &'a core::cell::Cell<u32>,
}

/// Overlapping fields, so no single field is independently committable.
#[derive(Clone, Copy)]
pub union U {
    pub flag: bool,
    pub byte: u8,
}

/// A state with a nested struct, an array and a large field that most bodies never touch, so the
/// `copied N of M bytes` report shows what copying only the used subset saves. 176 bytes: `header`
/// 12, `status` 4, `readings` 32, `history` 128.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Telemetry {
    pub header: Header,
    pub status: u32,
    pub readings: [u32; 8],
    pub history: [u64; 16],
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Header {
    pub id: u32,
    pub seq: u32,
    pub flags: u32,
}

/// A reference hidden one struct deep in a return type.
#[derive(Clone, Copy)]
pub struct View<'a> {
    pub counter: &'a u32,
}

#[inline(never)]
pub fn helper(state: &mut State) {
    state.counter += 1;
}

/// Declares `$name` with `#[rad_protected(shadow_only)]` and `$plain`, an unprotected twin with the
/// very same body, so `run_checks` can compare the two on the same inputs.
macro_rules! shadowed {
    (
        $(#[$meta:meta])*
        pub fn $name:ident / $plain:ident ($($params:tt)*) $(-> $ret:ty)? $body:block
    ) => {
        $(#[$meta])*
        #[rad_protected(shadow_only)]
        pub fn $name($($params)*) $(-> $ret)? $body

        #[inline(never)]
        pub fn $plain($($params)*) $(-> $ret)? $body
    };
}

// ---------------------------------------------------------------------------------------------
// Shadowed
// ---------------------------------------------------------------------------------------------

shadowed! {
    /// The baseline. The body runs entirely on the shadow, and only the one field it uses is copied
    /// in and back; `position.y`, `counter` and `samples` are never touched.
    ///
    /// Expected copy set: `.position.x`. Expected commit set: `.position.x`.
    pub fn basic_field / basic_field_plain(state: &mut State) {
        state.position.x += 1;
    }
}

shadowed! {
    /// The may-dirty set is a compile-time over-approximation: `position.x` is in it even on the
    /// path that does not write it. Copying an unchanged shadow field back is harmless, which is
    /// why every committed field is copied in too. Path-sensitive runtime dirtiness comes later.
    ///
    /// Expected copy set: `.position.x`. Expected commit set: `.position.x`.
    pub fn conditional_write / conditional_write_plain(state: &mut State, modify: bool) {
        if modify {
            state.position.x += 1;
        }
    }
}

shadowed! {
    /// A write to a parent covers a later write to its child, so the commit copies `position` once
    /// rather than the parent and then a field of it.
    ///
    /// Expected copy set: `.position`. Expected commit set: `.position` alone, not `.position` and
    /// `.position.x`.
    pub fn overlapping_writes / overlapping_writes_plain(state: &mut State, new_position: Position) {
        state.position = new_position;
        state.position.x = 7;
    }
}

shadowed! {
    /// Two unrelated fields stay two separate entries; nothing widens them to the whole `State`.
    ///
    /// Expected copy set: `.position.y`, `.counter`. Expected commit set: `.position.y`,
    /// `.counter`.
    pub fn sibling_fields / sibling_fields_plain(state: &mut State) {
        state.position.y = 5;
        state.counter += 1;
    }
}

shadowed! {
    /// Replacing the whole pointee gives the empty projection, so the copy-in and the commit both
    /// cover all of `State`, exactly as before the copy-in became per place.
    ///
    /// Expected copy set: the whole `*_original`. Expected commit set: the whole `*_original`.
    pub fn whole_state / whole_state_plain(state: &mut State, new_state: State) {
        *state = new_state;
    }
}

shadowed! {
    /// An index is not a fixed field path, so the projection is cut off before it and the whole
    /// array is copied in and committed. The copy-in has to cover the whole widened region: the
    /// commit writes back all of `samples`, including the elements the body never wrote.
    ///
    /// Expected copy set: `.samples`. Expected commit set: `.samples`, not `.samples[i]`.
    pub fn indexed_write / indexed_write_plain(state: &mut State, i: usize) {
        state.samples[i] = 9;
    }
}

shadowed! {
    /// The return value is computed from the shadow and returned normally: the commit statements go
    /// in front of the `Return`, so `_0` needs no special handling.
    ///
    /// Expected copy set: `.counter`, `.position.x`. Expected commit set: `.counter`.
    pub fn with_return_value / with_return_value_plain(state: &mut State) -> u32 {
        state.counter += 1;
        state.counter + state.position.x
    }
}

shadowed! {
    /// Every normal return gets its own copy of the commit statements.
    ///
    /// Expected copy set: `.counter`. Expected commit set: `.counter`, committed before each
    /// `Return`.
    pub fn multiple_returns / multiple_returns_plain(state: &mut State, early: bool) -> u32 {
        if early {
            return state.counter;
        }
        state.counter += 1;
        state.counter
    }
}

shadowed! {
    /// Only a `Return` commits. An unwind out of the body leaves the caller's state as it was,
    /// because the body only ever wrote the shadow.
    ///
    /// Expected copy set: `.counter`. Expected commit set: `.counter`.
    pub fn panics_before_commit / panics_before_commit_plain(state: &mut State, boom: bool) {
        state.counter += 1;
        if boom {
            panic!("shadow must not be committed");
        }
    }
}

shadowed! {
    /// A field that is only read is copied in but never committed.
    ///
    /// Expected copy set: `.header.id`, `.status`. Expected commit set: `.status`.
    /// Copies 8 of 176 bytes.
    pub fn read_only_field / read_only_field_plain(t: &mut Telemetry) {
        t.status += t.header.id;
    }
}

shadowed! {
    /// A field that is only written still has to be copied in: the commit is not tied to the path
    /// that wrote it, so the shadow must hold a defined value for it.
    ///
    /// Expected copy set: `.status`. Expected commit set: `.status`. Copies 4 of 176 bytes.
    pub fn write_only_field / write_only_field_plain(t: &mut Telemetry) {
        t.status = 7;
    }
}

shadowed! {
    /// Written only under an `if`: when the branch is not taken the commit copies back what the
    /// copy-in put there, so the caller's `status` is unchanged rather than garbage.
    ///
    /// Expected copy set: `.status`. Expected commit set: `.status`. Copies 4 of 176 bytes.
    pub fn write_under_if / write_under_if_plain(t: &mut Telemetry, set: bool) {
        if set {
            t.status = 1;
        }
    }
}

shadowed! {
    /// Nothing but `header.seq` is touched. `history`, `readings`, `status` and the rest of
    /// `header` are in neither set and are never copied.
    ///
    /// Expected copy set: `.header.seq`. Expected commit set: `.header.seq`. Copies 4 of 176
    /// bytes, where the whole-value copy took all 176.
    pub fn untouched_fields / untouched_fields_plain(t: &mut Telemetry) {
        t.header.seq += 1;
    }
}

shadowed! {
    /// Two sibling fields of a nested struct stay separate entries; neither set widens them to the
    /// parent `header`, so `header.seq` is not copied.
    ///
    /// Expected copy set: `.header.id`, `.header.flags`. Expected commit set: `.header.id`,
    /// `.header.flags`. Copies 8 of 176 bytes.
    pub fn nested_siblings / nested_siblings_plain(t: &mut Telemetry) {
        t.header.id = 1;
        t.header.flags |= 4;
    }
}

shadowed! {
    /// A constant index in an expression is *not* a `ConstantIndex` projection by the time this
    /// pass runs: MIR building lowers `t.readings[2]` to `readings[_n]` with `_n = const 2`, which
    /// canonicalization stops at, like any `Index`. The write is widened to the whole array.
    ///
    /// Expected copy set: `.readings`. Expected commit set: `.readings`. Copies 32 of 176 bytes.
    pub fn constant_index_expr / constant_index_expr_plain(t: &mut Telemetry) {
        t.readings[2] = 5;
    }
}

shadowed! {
    /// An array pattern does produce a `ConstantIndex` projection: the binding reads
    /// `readings[2 of 8]`, which canonicalizes to that one element. But the pattern also emits
    /// `PlaceMention(readings)` for the scrutinee, which counts as a use (as in the liveness
    /// analysis), so the copy-in is still widened to the whole array.
    ///
    /// Expected copy set: `.readings`, `.status`. Expected commit set: `.status`.
    /// Copies 36 of 176 bytes.
    pub fn constant_index_pattern / constant_index_pattern_plain(t: &mut Telemetry) {
        let [_, _, third, ..] = t.readings;
        t.status = third;
    }
}

shadowed! {
    /// A runtime index widens to the whole array in both sets.
    ///
    /// Expected copy set: `.readings`. Expected commit set: `.readings`. Copies 32 of 176 bytes.
    pub fn runtime_index / runtime_index_plain(t: &mut Telemetry, i: usize, v: u32) {
        t.readings[i] = v;
    }
}

shadowed! {
    /// A whole-value read uses the entire pointee, so the copy-in is the single whole copy the pass
    /// emitted before it became per place. The commit is still just the field that was written.
    ///
    /// Expected copy set: the whole `*_original`. Expected commit set: `.status`.
    /// Copies 176 of 176 bytes.
    pub fn whole_value_read / whole_value_read_plain(t: &mut Telemetry) -> u32 {
        let snapshot = *t;
        t.status = 3;
        snapshot.status + snapshot.header.id
    }
}

/// A shared reference inside the state takes the function out of scope, even though this body only
/// writes `counter`. The type is what is judged, not the body: `remember_counter` below shows the
/// same type being used to publish a borrow of the shadow into the caller's state.
#[rad_protected(shadow_only)]
pub fn shared_ref_state(state: &mut WithShared<'_>) {
    state.counter += 1;
}


// ---------------------------------------------------------------------------------------------
// Left alone, with the reason reported
// ---------------------------------------------------------------------------------------------

/// Rebasing writes onto several roots comes later.
#[rad_protected(shadow_only)]
pub fn two_mut_args(a: &mut State, b: &mut State) {
    a.counter += 1;
    b.counter += 1;
}

/// Duplicating and committing owned state needs the drop handling the baseline does not have.
#[rad_protected(shadow_only)]
pub fn non_copy_state(state: &mut Owned) {
    state.counter += 1;
}

/// A raw pointer inside the state could be written through to reach memory the shadow does not
/// cover.
#[rad_protected(shadow_only)]
pub fn raw_ptr_state(state: &mut WithPtr) {
    state.counter += 1;
}

/// A returned reference would point into the shadow and dangle once it is gone.
#[rad_protected(shadow_only)]
pub fn returns_reference(state: &mut State) -> &mut u32 {
    &mut state.counter
}

/// One struct deep is still reachable.
#[rad_protected(shadow_only)]
pub fn nested_raw_ptr_state(state: &mut Nested) {
    state.inner.counter += 1;
}

/// Before monomorphization the pass cannot see inside `T`, so a generic state stays out of scope
/// even when it is `Copy`.
#[rad_protected(shadow_only)]
pub fn generic_state<T: Copy>(state: &mut (T, u32)) {
    state.1 += 1;
}

/// A reference does not have to be the return type itself to dangle.
#[rad_protected(shadow_only)]
pub fn returns_nested_reference(state: &mut State) -> View<'_> {
    View { counter: &state.counter }
}

/// A mutable reborrow hands out a write capability the may-dirty set cannot follow, so the commit
/// could miss a field.
#[rad_protected(shadow_only)]
pub fn mutable_reborrow(state: &mut State) {
    helper(state);
}

/// Nothing to commit.
#[rad_protected(shadow_only)]
pub fn read_only(state: &mut State) -> u32 {
    state.counter + state.position.x
}

/// A `&` field can be overwritten with a borrow of the shadow. Committing `.label` would store a
/// pointer to the shadow local into the caller's state, where it dangles as soon as the function
/// returns. Borrowck cannot catch this: it ran long before this pass introduced the shadow.
#[rad_protected(shadow_only)]
pub fn remember_counter<'a>(state: &'a mut WithShared<'a>) {
    state.label = &state.counter;
}

/// Interior mutability defeats "a `&` cannot be written through": `Cell::set` mutates the caller's
/// memory directly, so the write escapes the shadow and an unwind cannot roll it back.
#[rad_protected(shadow_only)]
pub fn cell_escape(state: &mut WithCell<'_>) {
    state.counter += 1;
    state.external.set(99);
}

/// Union fields overlap, so `.flag` is not independent state. With `change == false` the body
/// never touches `flag`, but the commit would still read the union back at `bool` even when it
/// holds a `u8` that is not a valid `bool`.
#[rad_protected(shadow_only)]
pub fn union_write(u: &mut U, change: bool) {
    if change {
        u.flag = true;
    }
}

// ---------------------------------------------------------------------------------------------
// Runtime behaviour
// ---------------------------------------------------------------------------------------------

fn sample_state() -> State {
    State { position: Position { x: 10, y: 20 }, counter: 30, samples: [0, 1, 2, 3] }
}

fn other_state() -> State {
    State { position: Position { x: 1, y: 2 }, counter: 3, samples: [4, 5, 6, 7] }
}

fn sample_telemetry() -> Telemetry {
    let mut history = [0u64; 16];
    let mut i = 0;
    while i < history.len() {
        history[i] = 1000 + i as u64;
        i += 1;
    }
    Telemetry {
        header: Header { id: 11, seq: 22, flags: 1 },
        status: 40,
        readings: [1, 2, 3, 4, 5, 6, 7, 8],
        history,
    }
}

fn other_telemetry() -> Telemetry {
    Telemetry {
        header: Header { id: 0xdead, seq: u32::MAX - 1, flags: 0xf0 },
        status: 0,
        readings: [80, 70, 60, 50, 40, 30, 20, 10],
        history: [u64::MAX; 16],
    }
}

/// Every runtime expectation that does not need unwinding, so that the `no_std` build can run them
/// too. Returns the name of the first one that failed.
fn run_checks() -> Result<(), &'static str> {
    macro_rules! check {
        ($cond:expr, $name:expr) => {
            if !$cond {
                return Err($name);
            }
        };
    }

    let mut state = sample_state();
    basic_field(&mut state);
    check!(state.position.x == 11, "basic_field: the committed field reaches the caller");
    check!(state.position.y == 20, "basic_field: an uncommitted sibling field is untouched");
    check!(state.counter == 30, "basic_field: an uncommitted field is untouched");
    check!(state.samples == [0, 1, 2, 3], "basic_field: an uncommitted array is untouched");

    let mut state = sample_state();
    conditional_write(&mut state, false);
    check!(state == sample_state(), "conditional_write: the untaken branch changes nothing");
    conditional_write(&mut state, true);
    check!(state.position.x == 11, "conditional_write: the taken branch commits");

    let mut state = sample_state();
    overlapping_writes(&mut state, Position { x: 1, y: 2 });
    check!(state.position == Position { x: 7, y: 2 }, "overlapping_writes: parent commit wins");
    check!(state.counter == 30, "overlapping_writes: an unrelated field is untouched");

    let mut state = sample_state();
    sibling_fields(&mut state);
    check!(state.position == Position { x: 10, y: 5 }, "sibling_fields: only `y` is committed");
    check!(state.counter == 31, "sibling_fields: the sibling entry is committed too");

    let replacement =
        State { position: Position { x: 1, y: 2 }, counter: 3, samples: [4, 4, 4, 4] };
    let mut state = sample_state();
    whole_state(&mut state, replacement);
    check!(state == replacement, "whole_state: the whole pointee is committed");

    let mut state = sample_state();
    indexed_write(&mut state, 2);
    check!(state.samples == [0, 1, 9, 3], "indexed_write: the widened array commit is exact");
    check!(state.counter == 30, "indexed_write: an unrelated field is untouched");

    let mut state = sample_state();
    check!(with_return_value(&mut state) == 41, "with_return_value: `_0` survives the commit");
    check!(state.counter == 31, "with_return_value: the commit still happens");

    let mut state = sample_state();
    check!(multiple_returns(&mut state, true) == 30, "multiple_returns: early return value");
    check!(state.counter == 30, "multiple_returns: the early return commits the unchanged field");
    check!(multiple_returns(&mut state, false) == 31, "multiple_returns: late return value");
    check!(state.counter == 31, "multiple_returns: the late return commits");

    let mut state = sample_state();
    panics_before_commit(&mut state, false);
    check!(state.counter == 31, "panics_before_commit: the non-panicking path commits");

    let label = 7u32;
    let mut shared = WithShared { counter: 1, label: &label };
    shared_ref_state(&mut shared);
    check!(shared.counter == 2, "shared_ref_state: a shared reference in the state is fine");
    check!(*shared.label == 7, "shared_ref_state: the shared reference survives the round trip");

    let mut nested = Nested { inner: WithPtr { counter: 1, elsewhere: core::ptr::null_mut() } };
    nested_raw_ptr_state(&mut nested);
    check!(nested.inner.counter == 2, "nested_raw_ptr_state: unchanged behaviour");

    let mut generic = (1u8, 2u32);
    generic_state(&mut generic);
    check!(generic == (1, 3), "generic_state: unchanged behaviour");

    // Every shadowed function against its unprotected twin, on the same inputs: the caller's state
    // and the return value have to come out identical.
    macro_rules! same_as_plain {
        ($protected:ident, $plain:ident, $init:expr $(, $arg:expr)*) => {{
            let mut protected = $init;
            let mut plain = $init;
            let protected_ret = $protected(&mut protected $(, $arg)*);
            let plain_ret = $plain(&mut plain $(, $arg)*);
            check!(
                protected == plain && protected_ret == plain_ret,
                concat!(stringify!($protected), ": differs from its unprotected twin")
            );
        }};
    }

    for state in [sample_state(), other_state()] {
        same_as_plain!(basic_field, basic_field_plain, state);
        same_as_plain!(conditional_write, conditional_write_plain, state, false);
        same_as_plain!(conditional_write, conditional_write_plain, state, true);
        same_as_plain!(
            overlapping_writes,
            overlapping_writes_plain,
            state,
            Position { x: 1, y: 2 }
        );
        same_as_plain!(sibling_fields, sibling_fields_plain, state);
        same_as_plain!(whole_state, whole_state_plain, state, other_state());
        for i in 0..4 {
            same_as_plain!(indexed_write, indexed_write_plain, state, i);
        }
        same_as_plain!(with_return_value, with_return_value_plain, state);
        same_as_plain!(multiple_returns, multiple_returns_plain, state, true);
        same_as_plain!(multiple_returns, multiple_returns_plain, state, false);
        same_as_plain!(panics_before_commit, panics_before_commit_plain, state, false);
    }

    for t in [sample_telemetry(), other_telemetry()] {
        same_as_plain!(read_only_field, read_only_field_plain, t);
        same_as_plain!(write_only_field, write_only_field_plain, t);
        same_as_plain!(write_under_if, write_under_if_plain, t, false);
        same_as_plain!(write_under_if, write_under_if_plain, t, true);
        same_as_plain!(untouched_fields, untouched_fields_plain, t);
        same_as_plain!(nested_siblings, nested_siblings_plain, t);
        same_as_plain!(constant_index_expr, constant_index_expr_plain, t);
        same_as_plain!(constant_index_pattern, constant_index_pattern_plain, t);
        for i in 0..8 {
            same_as_plain!(runtime_index, runtime_index_plain, t, i, 100 + i as u32);
        }
        same_as_plain!(whole_value_read, whole_value_read_plain, t);
    }

    // The not-taken branch must leave the caller's field as it was, not as whatever the shadow
    // held before the copy-in.
    let mut t = sample_telemetry();
    write_under_if(&mut t, false);
    check!(t == sample_telemetry(), "write_under_if: the untaken branch changes nothing");
    let mut t = sample_telemetry();
    runtime_index(&mut t, 5, 0);
    check!(t.readings == [1, 2, 3, 4, 5, 0, 7, 8], "runtime_index: the other elements survive");

    // The functions the pass leaves alone must still behave exactly as written.
    let mut state = sample_state();
    let mut other = state;
    two_mut_args(&mut other, &mut state);
    check!(state.counter == 31 && other.counter == 31, "two_mut_args: unchanged behaviour");
    mutable_reborrow(&mut state);
    check!(state.counter == 32, "mutable_reborrow: unchanged behaviour");
    check!(read_only(&mut state) == 42, "read_only: unchanged behaviour");

    Ok(())
}

#[cfg(not(rad_no_std))]
fn main() {
    if let Err(name) = run_checks() {
        panic!("function_shadow: FAILED: {name}");
    }

    // Needs unwinding, so it is not part of `run_checks`: the body writes the shadow and then
    // panics, and the caller's state must come out untouched.
    let mut state = sample_state();
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        panics_before_commit(&mut state, true)
    }));
    assert!(unwound.is_err(), "function_shadow: the body was expected to panic");
    assert_eq!(
        state.counter, 30,
        "function_shadow: FAILED: panics_before_commit: an unwind leaves the original intact",
    );

    println!("function_shadow: all runtime checks passed");
}

#[cfg(rad_no_std)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

/// `core` is built for unwinding, so a `panic=abort` `no_std` binary has to supply the personality
/// symbol its rlib still references. Nothing ever unwinds here.
#[cfg(rad_no_std)]
#[unsafe(no_mangle)]
pub extern "C" fn rust_eh_personality() {}

#[cfg(rad_no_std)]
unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

#[cfg(rad_no_std)]
unsafe fn report(msg: &str) {
    write(2, msg.as_ptr(), msg.len());
    write(2, "\n".as_ptr(), 1);
}

#[cfg(rad_no_std)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    match run_checks() {
        Ok(()) => {
            report("function_shadow: all runtime checks passed");
            0
        }
        Err(name) => {
            report("function_shadow: FAILED:");
            report(name);
            1
        }
    }
}
