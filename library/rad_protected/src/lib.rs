//! The Rad-Rust `rad_protected` Runtime
//! 
//! This library contains a static runtime for running software radiation-hardened programs through TMR.
//! 
//! The runtime is intended to be used with a rustc fork to generate runtime calls,
//! and thus only meant to be referenced directly by the compiler itself.
//! 
//! For porting this library to a new target, see mini_std/mod.rs

#![feature(rustc_attrs)]
#![feature(staged_api)]
#![allow(internal_features)]
#![no_std]

/// `rad_protected` runtime module
#[stable(feature = "rad_protected", since = "1.95.0")]
pub mod runtime;

mod fork;
mod libc_helpers;
mod role;
mod mini_std;
mod shared_memory;
