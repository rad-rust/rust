#![feature(rustc_attrs)]
#![feature(staged_api)]
#![allow(internal_features)]
#![no_std]

/// `rad_protected` runtime module
#[stable(feature = "rad_protected", since = "1.95.0")]
pub mod runtime;

mod checkpoint;
mod hal;
