//! A MIPS emulator written entirely in Rust.

#![warn(missing_docs)]
#![feature(plugin)]
#![plugin(docopt_macros)]

extern crate byteorder;
extern crate rustc_serialize;
extern crate docopt;
#[macro_use] extern crate log;
extern crate env_logger;

pub mod processor;
pub mod constants;
pub mod helpers;

pub use processor::{Processor, Instruction, parse_instruction};
