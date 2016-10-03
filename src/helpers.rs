//! A module full of useful miscellaneous functions that help automate
//! boring jobs like creating the machine code representation of an
//! instruction.
#![allow(dead_code)]

use byteorder::{BigEndian, WriteBytesExt};
use std::mem::transmute;


/// Convert a list of big endian instructions to a byte array.
pub fn instructions_to_bytes(instructions: Vec<u32>) -> Vec<u8> {
    let mut buf = vec![];
    for inst in instructions {
        buf.write_u32::<BigEndian>(inst).unwrap();
    }
    buf
}

/// A simple helper that creates an add instruction.
///
/// Converts something like `add r4,r2,r4` into its corresponding
/// machine code instruction.
pub fn add_instruction(rd: usize, rs: usize, rt: usize) -> u32 {
    make_r_instruction(0, rs, rt, rd, 0, 0b100000)
}

/// Create a syscall instruction. Pretty much just gives you back
/// the constant `0xC`.
pub fn syscall_instruction() -> u32 {
    // A syscall is really just an R instruction with a funct of 12
    0xc
}

/// Create an instruction for jumping to a particular address.
pub fn jump_instruction(addr: i32) -> u32 {
    let opcode = 0x02;

    // Transmute the address from an i32 to a u32
    // This is perfectly safe because they are the same size and
    // we're just changing what the compiler interprets the bits as
    let addr = unsafe { transmute::<i32, u32>(addr) };

    // Discard the last two bits because we know an address is always
    // a multiple of 4
    let addr = addr >> 2;

    // Make sure the leading 6 bits are zeroes so we can fit the opcode in
    assert!(addr.leading_zeros() >= 6);

    opcode << 26 | addr
}

/// Create a generic R instruction.
pub fn make_r_instruction(opcode: usize,
                          rs: usize,
                          rt: usize,
                          rd: usize,
                          shift: usize,
                          funct: usize)
                          -> u32 {
    // Do a bounds check and panic if we tried to make an invalid
    // instruction
    assert!(opcode < (1 << 6));
    assert!(rs < (1 << 5));
    assert!(rt < (1 << 5));
    assert!(rd < (1 << 5));
    assert!(shift < (1 << 5));
    assert!(funct < (1 << 6));

    let inst = opcode << 26 | rs << 21 | rt << 16 | rd << 11 | shift << 6 | funct;

    inst as u32
}

/// Create a generic R instruction.
pub fn make_i_instruction(opcode: usize, rs: usize, rt: usize, imm: u32) -> u32 {
    // Do a bounds check and panic if we tried to make an invalid
    // instruction
    assert!(opcode < (1 << 6));
    assert!(rs < (1 << 5));
    assert!(rt < (1 << 5));
    assert!(imm < (1 << 16));

    let inst = opcode << 26 | rs << 21 | rt << 16 | imm as usize;

    inst as u32
}


#[cfg(test)]
mod test {
    use super::*;
    use constants::*;

    #[test]
    fn make_r_instruction_gives_expected() {
        let got = make_r_instruction(0, 26, 4, 31, 29, 11);
        let should_be = 0b000000_11010_00100_11111_11101_001011;
        assert_eq!(got, should_be);
    }

    #[test]
    #[should_panic]
    fn invalid_opcode_panics() {
        make_r_instruction(64, 0, 0, 0, 0, 0);
    }
    #[test]
    #[should_panic]
    fn make_r_with_invalid_opcode_panics() {
        make_r_instruction(64, 0, 0, 0, 0, 0);
    }

    #[test]
    #[should_panic]
    fn make_r_with_invalid_rs_panics() {
        make_r_instruction(0, 32, 0, 0, 0, 0);
    }

    #[test]
    #[should_panic]
    fn make_r_with_invalid_rt_panics() {
        make_r_instruction(0, 0, 32, 0, 0, 0);
    }

    #[test]
    #[should_panic]
    fn make_r_with_invalid_rd_panics() {
        make_r_instruction(0, 0, 0, 32, 0, 0);
    }

    #[test]
    #[should_panic]
    fn make_r_with_invalid_shift_panics() {
        make_r_instruction(0, 0, 0, 0, 32, 0);
    }

    #[test]
    #[should_panic]
    fn make_r_with_invalid_funct_panics() {
        make_r_instruction(0, 0, 0, 0, 0, 64);
    }

    #[test]
    fn instructions_to_bytes_single_instruction() {
        let instructions = vec![
            make_r_instruction(0, 0, 0, 0, 0, 0), // no-op
        ];
        let should_be: Vec<u8> = vec![0, 0, 0, 0];
        let got = instructions_to_bytes(instructions);
        assert_eq!(got, should_be);
    }

    #[test]
    fn instructions_to_bytes_multiple_instructions() {
        let instructions = vec![
            add_instruction(1, 1, 2),
            add_instruction(5, 1, 8),
        ];
        let should_be: Vec<u8> = vec![
            0, 34, 8, 32,  // 0b000000_00001_00010_00001_00000_100000
            0, 40, 40, 32,    // 0b000000_00001_01000_00101_00000_000000
        ];
        let got = instructions_to_bytes(instructions);
        assert_eq!(got, should_be);
    }

    #[test]
    fn create_valid_jump_instruction() {
        let addr = 0b0000_0011__1111_1111__0000_1111__0000_1100;
        let got = jump_instruction(addr);
        let should_be = 0b0000_1000__1111_1111__1100_0011__1100_0011;
        assert_eq!(got, should_be);
    }

    #[test]
    #[should_panic]
    fn invalid_jump() {
        // The first 4 bits must be zeroes because that's where our
        // opcode will end up going. Likewise the last 4 must be zeroes
        // because all instructions are word aligned
        let addr: i32 = 128;
        assert_eq!(addr.leading_zeros(), 2);
        jump_instruction(addr);
    }

    #[test]
    fn syscall_generates_constant() {
        assert_eq!(syscall_instruction(), 12);
    }

    #[test]
    fn create_valid_imm_instruction() {
        let opcode = OP_ORI as usize;  // 0b0000_1101
        let rs: usize = TEMP_1;  // 0b0000_1001
        let rt: usize = TEMP_0;  // 0b0000_1000
        let imm: u32 = 42;  // 0b101010
        let got = make_i_instruction(opcode, rs, rt, imm);
        let should_be = 0b001101_01001_01000_0000000000101010;
        assert_eq!(got, should_be as u32);
    }
}
