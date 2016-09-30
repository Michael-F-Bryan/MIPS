//! The central processing unit for this MIPS emulator.
//!
//! The registers used, and their common names, are as follows:
//!
//! Number         Name           Comments
//! ======         ====           ========
//! $0             $zero          Always zero
//! $1             $at            Reserved for assembler
//! $2, $3         $v0, $v1       First and second return values, respectively
//! $4, ..., $7    $a0, ..., $a3  First four arguments to functions
//! $8, ..., $15   $t0, ..., $t7  Temporary registers
//! $16, ..., $23  $s0, ..., $s7  Saved registers //! $24, $25       $t8, $t9       More temporary registers //! $26, $27       $k0, $k1       Reserved for kernel (operating system)
//! $28            $gp            Global pointer
//! $29            $sp            Stack pointer
//! $30            $fp            Frame pointer
//! $31            $ra            Return address


use std::io::Cursor;
use byteorder::{ByteOrder, BigEndian, ReadBytesExt};


// Define some constants to make accessing the individual registers easier
const ZERO: usize = 0;
const RET_1: usize = 2;
const RET_2: usize = 3;
const GLOBAL_POINTER: usize = 28;
const STACK_POINTER: usize = 29;
const FRAME_POINTER: usize = 30;
const RETURN_ADDRESS: usize = 31;


#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    /// An R instruction (e.g. add $s1, $s2, $s3)
    ///
    /// - opcode: machinecode representation of the instruction mnemonic
    /// - rs, rt: source registers
    /// - rd: destination register
    /// - shift: used with the shift and rotate instructions
    /// - funct: for instructions that share an opcode
    ///
    /// R(opcode, rd, rs, rt, shift, funct),
    R(u8, u8, u8, u8, u8, u8),

    /// An invalid instruction.
    Invalid,
}


#[allow(dead_code)]
pub struct Processor {
    /// Store RAM as a big array of bytes (2^16).
    memory: Vec<u8>,

    /// The 32 registers
    registers: [u32; 32],

    pc: usize,
}


impl Processor {
    pub fn new() -> Processor {
        Processor::default()
    }

    /// Load a MIPS program (list of bytes) into memory starting at
    /// address 0x00
    pub fn load(&mut self, program: Vec<u8>) -> Result<usize, String> {
        // Check we won't overflow RAM
        if program.len() > self.memory.len() {
            return Err("Program won't fit in memory".to_string());
        }

        let num_bytes = program.len();

        // Set the program counter to the program's start
        self.pc = 0;

        // Otherwise, copy the program in element-wise
        for (i, code) in program.into_iter().enumerate() {
            self.memory[i] = code;
        }
        Ok(num_bytes)
    }

    /// Get the next instruction (as 32 bit endian big word).
    pub fn next_instruction(&self) -> Result<u32, String> {
        if self.pc+3 >= self.memory.len() {
            return Err(format!("Trying to access memory outside of RAM at index {:#}",
                               self.pc));
        }

        let instruction = &self.memory[self.pc..self.pc+4];
        Ok(BigEndian::read_u32(instruction))
    }

    /// Load and execute the next instruction.
    pub fn step(&mut self) -> Result<(), String> {
        let next = try!(self.next_instruction());
        let instruction = parse_instruction(next);
        unimplemented!()
    }

}

impl Default for Processor {
    fn default() -> Processor {
        Processor { memory: vec![0; 65536],
                    registers: [0; 32],
                    pc: 0,
        }
    }
}


#[inline]
pub fn parse_instruction(inst: u32) -> Instruction {
    let opcode = (inst >> 26) as u8;  // Grab the top 6 bits

    // Check what type of instruction we have (R, I, J)
    match opcode {
        _ => {
            // An R instruction
            // opcode rs rt rd shift funct
            //      6  5  5  5     5     6
            let rs = ((inst >> 21) & 0b0001_1111) as u8;
            let rt = ((inst >> 16) & 0b0001_1111) as u8;
            let rd = ((inst >> 11) & 0b0001_1111) as u8;
            let shift = ((inst >> 6) & 0b0001_1111) as u8;
            let funct = (inst & 0b0011_1111) as u8;

            Instruction::R(opcode, rs, rt, rd, shift, funct)
        }
    }
}


#[test]
fn constructor() {
    let got = Processor::new();
    assert_eq!(got.registers, [0; 32]);
    assert_eq!(got.memory.len(), 65536);
}

#[test]
fn load_empty_program() {
    let program: Vec<u8> = Vec::new();
    let mut cpu = Processor::new();
    let got = cpu.load(program);
    assert_eq!(got, Ok(0));

    // Make sure the entire memory is still full of zeroes
    assert!(cpu.memory.to_vec() == vec![0; 65536]);
}

#[test]
fn load_42_sevens() {
    let program: Vec<u8> = vec![0x07; 42];
    let mut cpu = Processor::new();
    let got = cpu.load(program);
    assert_eq!(got, Ok(42));

    // Double check the first 42 elements equal 7
    assert!(cpu.memory
            .to_vec()
            .iter()
            .take(42)
            .all(|e| *e == 0x07));

    // And make sure the rest of RAM is still zeroed out
    assert!(cpu.memory
            .to_vec()
            .iter()
            .skip(42)
            .all(|e| *e == 0x00));
}

#[test]
fn get_next_instruction() {
    let program: Vec<u8> = vec![0x07; 42];
    let mut cpu = Processor::new();
    assert_eq!(cpu.next_instruction(), Ok(0x00));
    cpu.load(program).unwrap();
    assert_eq!(cpu.next_instruction(), Ok(0x07070707));
}

#[test]
fn extract_r_instruction() {
    // Check a super basic instruction first
    let inst = 0xff_ff_ff_ff;
    println!("{:#b}", inst);
    let got = parse_instruction(inst);
    let should_be = Instruction::R(63, 31, 31, 31, 31, 63);
    println!("{:?}", got);
    assert_eq!(got, should_be);

    let mut inst = 0b00;
    let opcode = 0b0011_1111 << 26;  // 63
    let rs = 0b0001_1010 << 21;  // 26
    let rt = 0b0000_0100 << 16;  // 4
    let rd = 0b0001_1111 << 11;  // 31
    let shift = 0b0001_1101 << 6;  // 29
    let funct = 0b0000_1011;  // 11

    inst = (inst
            |opcode
            | rs
            | rt
            | rd
            | shift
            | funct);

    // Double check we composed the instruction right
    assert_eq!(inst, 0b111111_11010_00100_11111_11101_001011);

    let got = parse_instruction(inst);
    let should_be = Instruction::R(63, 26, 4, 31, 29, 11);
    println!("{:?}", got);
    assert_eq!(got, should_be);
}
