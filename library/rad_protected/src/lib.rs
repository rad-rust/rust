#![feature(rustc_attrs)]
#![feature(staged_api)]
#![allow(internal_features)]
#![no_std]

/// `rad_protected` runtime module
#[stable(feature = "rad_protected", since = "1.95.0")]
pub mod runtime;

// TODO: Rather than exporting this crate through std, allow #[no_std] environments with
// a custom target, where this crate is linked through sysroot provided the given target matches
