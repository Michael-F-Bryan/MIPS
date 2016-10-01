//! Define some constants to make accessing the individual registers easier

#![allow(dead_code)]

pub const ZERO: usize = 0;
pub const RET_1: usize = 2;
pub const RET_2: usize = 3;
pub const GLOBAL_POINTER: usize = 28;
pub const STACK_POINTER: usize = 29;
pub const FRAME_POINTER: usize = 30;
pub const RETURN_ADDRESS: usize = 31;

// funct codes for R instructions
pub const FUNCT_ADD: u8 = 0x20;
pub const FUNCT_AND: u8 = 0x24;
