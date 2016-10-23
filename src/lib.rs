//! A MIPS emulator written entirely in Rust.

// So we can use the docopt!() macro
#![feature(plugin)]
#![plugin(docopt_macros)]

// Extra lints
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![deny(missing_copy_implementations)]
#![deny(trivial_casts)]
#![deny(trivial_numeric_casts)]
#![deny(unused_import_braces)]
#![deny(unused_qualifications)]
#![deny(unused_imports)]

// Support for using clippy
#![cfg_attr(feature = "dev", plugin(clippy))]

extern crate byteorder;
extern crate rustc_serialize;
extern crate docopt;
#[macro_use]
extern crate log;
extern crate env_logger;

pub mod processor;
pub mod constants;
pub mod helpers;
pub mod assembler;

pub use processor::{Processor, Instruction, parse_instruction};
