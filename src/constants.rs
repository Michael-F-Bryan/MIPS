//! Define some constants to make accessing individual registers easier.

#![allow(dead_code)]
#![allow(missing_docs)]

pub const ZERO: usize = 0;
pub const RET_1: usize = 2;
pub const RET_2: usize = 3;
pub const GLOBAL_POINTER: usize = 28;
pub const STACK_POINTER: usize = 29;
pub const FRAME_POINTER: usize = 30;
pub const RETURN_ADDRESS: usize = 31;

// Argument registers
pub const ARG_0: usize = 4;
pub const ARG_1: usize = 5;
pub const ARG_2: usize = 6;
pub const ARG_3: usize = 7;

// Temporary registers
pub const TEMP_0: usize = 8;
pub const TEMP_1: usize = 9;
pub const TEMP_2: usize = 10;
pub const TEMP_3: usize = 11;
pub const TEMP_4: usize = 12;
pub const TEMP_5: usize = 13;
pub const TEMP_6: usize = 14;
pub const TEMP_7: usize = 15;

// funct codes for R instructions
pub const FUNCT_ADD: u8 = 0x20;
pub const FUNCT_AND: u8 = 0x24;
pub const FUNCT_DIV: u8 = 0x1C;
pub const FUNCT_MULT: u8 = 0x18;

pub const JMP: u8 = 0x02;

// opcodes for I instructions
pub const OP_ORI: u8 = 0x0D;
pub const OP_ADDI: u8 = 0x08;
