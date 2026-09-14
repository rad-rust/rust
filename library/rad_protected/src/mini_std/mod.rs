//! A near-faithful recreation and extension of the minimal subset of `std` required by `rad_protected`
//! for `no_std` environments.
//!
//! This module provides a `std`-like API to isolate platform-specific functionality.
//!
//! The current implementation targets Linux, but it is intended to be reimplemented for
//! other platforms as needed.
//!
//! Because this module mirrors the `std` API, it can be removed entirely on platforms 
//! where the standard library is available, other than the IPC module.
//! 
//! Since some `rad_protected` functions are guaranteed to invoke certain `mini_std` 
//! functions from a single thread, synchronization is not uniformly implemented throughout this module.
//! 
//! Be careful when using these APIs, as they may not be thread-safe outside of their intended usage.

pub mod io;
pub mod sync;
pub mod fs;
pub mod ipc;
