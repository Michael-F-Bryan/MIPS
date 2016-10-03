//! The central processing unit for this MIPS emulator.
//! //! The registers used, and their common names, are as follows:
//!
//!     Number        |  Name           | Comments
//!     --------------+-----------------+---------
//!     $0            |  $zero          | Always zero
//!     $1            |  $at            | Reserved for assembler
//!     $2, $3        |  $v0, $v1       | First and second return values, respectively
//!     $4, ..., $7   |  $a0, ..., $a3  | First four arguments to functions
//!     $8, ..., $15  |  $t0, ..., $t7  | Temporary registers
//!     $16, ..., $23 |  $s0, ..., $s7  | Saved registers
//!     $24, $25      |  $t8, $t9       | More temporary registers
//!     $26, $27      |  $k0, $k1       | Reserved for kernel (operating system)
//!     $28           |  $gp            | Global pointer
//!     $29           |  $sp            | Stack pointer
//!     $30           |  $fp            | Frame pointer
//!     $31           |  $ra            | Return address //! //! MIPS uses the following opcodes:
//!
//! Here is a list of all the instructions supported by MIPS:
//!
//! Mnemonic |  Meaning                  | Type   |  Opcode    |  Funct
//! ---------+---------------------------+--------+------------+-------
//! add      |  Add                      | R      |  0x00      |  0x20
//! addi     |  Add Immediate            | I      |  0x08      |  NA
//! addiu    |  Add Unsigned Immediate   | I      |  0x09      |  NA
//! addu     |  Bitwise Add Unsigned     | R      |  0x00      |  0x21
//! and      |  Bitwise AND              | R      |  0x00      |  0x24
//! andi     |  Bitwise AND Immediate    | I      |  0x0C      |  NA
//! beq      |  Branch if Equal          | I      |  0x04      |  NA
//! bne      |  Branch Not Equal         | I      |  0x05      |  NA
//! div      |  Divide                   | R      |  0x00      |  x1A
//! divu     |  Unsigned Divide          | R      |  0x00      |  0x1B
//! j        |  Jump to Address          | J      |  0x02      |  NA
//! jal      |  Jump and Link            | J      |  0x03      |  NA
//! jr       |  Jump to Address          | R      |  0x00      |  0x08
//! lbu      |  Load Byte Unsigned       | I      |  0x24      |  NA
//! lhu      |  Load Halfword Unsigned   | I      |  0x25      |  NA
//! lui      |  Load Upper Immediate     | I      |  0x0F      |  NA
//! lw       |  Load Word                | I      |  0x23      |  NA
//! mfhi     |  Move from HI Register    | R      |  0x00      |  0x10
//! mflo     |  Move from LO Register    | R      |  0x00      |  0x12
//! mfc0     |  Move from Coprocessor 0  | R      |  0x10      |  NA
//! mult     |  Multiply                 | R      |  0x00      |  0x18
//! multu    |  Unsigned Multiply        | R      |  0x00      |  0x19
//! nor      |  Bitwise NOR              | R      |  0x00      |  0x27
//! xor      |  Bitwise XOR              | R      |  0x00      |  0x26
//! or       |  Bitwise OR               | R      |  0x00      |  0x25
//! ori      |  Bitwise OR Immediate     | I      |  0x0D      |  NA
//! sb       |  Store Byte               | I      |  0x28      |  NA
//! sh       |  Store Halfword           | I      |  0x29      |  NA
//! slt      |  Set to 1 if Less Than    | R      |  0x00      |  0x2A
//! slti     |  Set to 1 if Less         | I      |  0x0A      |  NA
//!          |      Than Immediate
//! sltiu    |  Set to 1 if Less Than    | I      |  0x0B      |  NA
//!          |      Unsigned Immediate
//! sltu     |  Set to 1 if Less Than    | R      |  0x00      |  0x2B
//!          |      Unsigned
//! sll      |  Logical Shift Left       | R      |  0x00      |  0x00
//! srl      |  Logical Shift Right      | R      |  0x00      |  0x02
//! sra      |  Arithmetic Shift Right   | R      |  0x00      |  0x03
//! sub      |  Subtract                 | R      |  0x00      |  0x22
//! subu     |  Unsigned Subtract        | R      |  0x00      |  0x23
//! sw       |  Store Word               | I      |  0x2B      |  NA


use byteorder::{ByteOrder, BigEndian};
use constants::*;
use std::fmt::{Debug, Formatter};
use std::mem::transmute;


/// A representation of a single MIPS instruction or an invalid instruction.
#[derive(Clone, Copy, PartialEq)]
pub enum Instruction {
    /// An R instruction (e.g. add $s1, $s2, $s3)
    ///
    /// - rs, rt: source registers
    /// - rd: destination register
    /// - shift: used with the shift and rotate instructions
    /// - funct: for instructions that share an opcode
    ///
    /// R(rd, rs, rt, shift, funct),
    R(u8, u8, u8, u8, u8),

    /// A Jump instruction takes the target address as its only argument
    J(i32),

    /// A syscall that uses the contents of $v0 to decide which function
    /// to run.
    ///
    /// Here are some of the more common syscall codes:
    ///
    /// code  |  call           |  arguments                  |  results
    /// ------+-----------------+-----------------------------+---------
    /// 1     |  print integer  |  $a0 = integer to print     |
    /// 2     |  print float    |  $f12 = float to print      |
    /// 3     |  print double   |  $f12 = float to print      |
    /// 4     |  print string   |  $a0 = address of           |
    ///       |                 |      beginning of string    |
    /// 5     |  read integer   |                             |  integer stored in $v0
    /// 6     |  read float     |                             |  float stored in $f0
    /// 7     |  read double    |                             |  double stored in $f0
    /// 8     |  read string    |  $a0 = pointer to buffer,   |  string stored in buffer
    ///       |                 |      $a1 = length of buffer |
    /// 9     |  sbrk (allocate |  $a0 = size needed          |  $v0 = address of buffer
    ///       |  memory buffer) |                             |
    /// 10    |  exit           |                             |
    Syscall,

    /// An I instruction formatted as Immediate(opcode, rs, rt, imm).
    I(u8, u8, u8, u32),

    /// - opcode: machinecode representation of the instruction mnemonic
    /// An invalid instruction.
    Invalid,

    /// A no-op instruction
    Noop,
}

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        match *self {
            Instruction::R(rd, rs, rt, shift, funct) => {
                write!(f,
                       "R({:#x}, {:#x}, {:#x}, {:#x}, {:#x})",
                       rd,
                       rs,
                       rt,
                       shift,
                       funct)
            }

            Instruction::I(opcode, rs, rt, imm) => {
                write!(f, "I({:#x}, {:#x}, {:#x}, {})", opcode, rs, rt, imm)
            }

            Instruction::J(addr) => write!(f, "J({:#x})", addr),
            Instruction::Syscall => write!(f, "Syscall"),
            Instruction::Invalid => write!(f, "Invalid"),
            Instruction::Noop => write!(f, "Noop"),
        }
    }
}


/// A struct representing the state of the MIPS processor.
///
/// It contains an infinitely long array of bytes for RAM,
/// some registers, and the program counter.
#[allow(dead_code)]
pub struct Processor {
    /// Store RAM as a big array of bytes (2^16).
    pub memory: Vec<u8>,

    /// The 32 registers
    pub registers: [u32; 32],

    /// The program counter - a pointer to the next instruction in memory.
    pub pc: usize,

    stopped: bool,
}


impl Debug for Processor {
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "Processor(pc={}, stopped={})", self.pc, self.stopped)
    }
}

impl Default for Processor {
    fn default() -> Processor {
        Processor {
            stopped: false,
            memory: vec![0; 65536],
            registers: [0; 32],
            pc: 0,
        }
    }
}


impl Processor {
    /// Create a new processor with its memory and registers cleared.
    pub fn new() -> Processor {
        Processor::default()
    }

    /// Start the emulator. It will keep running until there is either
    /// an exit syscall, or an error.
    pub fn start(&mut self) -> Result<(), String> {
        while self.running() {
            let result = self.step();
            if result.is_err() {
                return result;
            }
        }

        Ok(())
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

    /// Get the next instruction (as 32 bit endian big word) and update the
    /// program counter.
    pub fn next_instruction(&mut self) -> Result<u32, String> {
        if self.pc + 3 >= self.memory.len() {
            return Err(format!("Trying to access memory outside of RAM at index {:#}",
                               self.pc));
        }

        let instruction = &self.memory[self.pc..self.pc + 4];
        self.pc += 4;
        Ok(BigEndian::read_u32(instruction))
    }

    /// Load and execute the next instruction.
    pub fn step(&mut self) -> Result<(), String> {
        let next = try!(self.next_instruction());
        let instruction = parse_instruction(next);
        trace!("{:?}", instruction);

        match instruction {
            Instruction::Noop => {
                warn!("Reached null instruction. Terminating program.");
                self.stopped = true;
                Ok(())
            }

            Instruction::R(rd, rs, rt, shift, funct) => {
                self.handle_r_instruction(rd, rs, rt, shift, funct)
            }

            Instruction::J(offset) => {
                // Add the offset to the program counter, making sure to
                // subtract 4 because the next_instruction() function
                // incremented the program counter
                self.pc += offset as usize - 4;
                debug!("Jumping to {:#x}", self.pc);
                Ok(())
            }

            // Execute a syscall. Note that $v0 must be set with the code of the
            // function you want to call first.
            Instruction::Syscall => {
                let arg = self.registers[RET_1];
                self.handle_syscall(arg)
            }

            Instruction::I(opcode, rs, rt, imm) => self.handle_i_instruction(opcode, rs, rt, imm),

            Instruction::Invalid => Err(format!("Invalid instruction: {:#b}", next)),
        }

    }

    /// Execute a syscall.
    fn handle_syscall(&mut self, arg: u32) -> Result<(), String> {
        match arg {
            // exit
            10 => {
                self.stopped = true;
                info!("Stopping Emulator");
                Ok(())
            }

            // print integer in $a0
            1 => {
                let value = self.registers[ARG_0];
                debug!("Printing integer: {}", value);
                print!("{}", value);
                Ok(())
            }

            _ => Err(format!("Unknown syscall: {}", arg)),
        }
    }


    /// Evaluate a single R instruction, returning Ok() or an error message
    /// if it fails.
    fn handle_r_instruction(&mut self,
                            rd: u8,
                            rs: u8,
                            rt: u8,
                            shift: u8,
                            funct: u8)
                            -> Result<(), String> {
        match funct {
            FUNCT_ADD => {
                let a = self.registers[rs as usize];
                let b = self.registers[rt as usize];
                self.registers[rd as usize] = a + b;
                debug!("${} = {} + {}", rd, a, b);
                Ok(())
            }

            FUNCT_AND => {
                self.registers[rd as usize] = self.registers[rs as usize] &
                                              self.registers[rt as usize];
                Ok(())
            }

            FUNCT_DIV => {
                self.registers[rd as usize] = self.registers[rs as usize] /
                                              self.registers[rt as usize];
                Ok(())
            }

            FUNCT_MULT => {
                self.registers[rd as usize] = self.reg(rs) * self.reg(rt);
                Ok(())
            }

            // Otherwise we don't know what this one is
            unknown => Err(format!("Unknown funct: {:#b}", unknown)),
        }
    }

    /// Evaluate a single I instruction.
    fn handle_i_instruction(&mut self, opcode: u8, rs: u8, rt: u8, imm: u32) -> Result<(), String> {
        match opcode {
            OP_ORI => {
                self.registers[rs as usize] = self.reg(rt) | imm;
                Ok(())
            }

            unknown => Err(format!("Unknown opcode: {:#b}", unknown)),
        }
    }

    /// Get the value of a register
    #[inline]
    pub fn reg(&self, index: u8) -> u32 {
        self.registers[index as usize]
    }

    /// Get the program counter's current value.
    pub fn program_counter(&self) -> usize {
        self.pc
    }

    /// Check whether the emulator is running or not.
    pub fn running(&self) -> bool {
        !self.stopped
    }
}

/// Parse a single MIPS instruction and break it up into its
/// constituent components (opcode, data, etc).
#[inline]
pub fn parse_instruction(inst: u32) -> Instruction {
    if inst == 0xc {
        return Instruction::Syscall;
    }

    if inst == 0x00 {
        return Instruction::Noop;
    }

    let opcode = ((inst >> 26) & 0b0011_1111) as u8;  // Grab the top 6 bits

    // Check what type of instruction we have (R, I, J)
    match opcode {
        // For R-format instructions, the opcode is always zero
        0 => {
            // An R instruction
            // opcode rs rt rd shift funct
            //      6  5  5  5     5     6
            let rs = ((inst >> 21) & 0b0001_1111) as u8;
            let rt = ((inst >> 16) & 0b0001_1111) as u8;
            let rd = ((inst >> 11) & 0b0001_1111) as u8;
            let shift = ((inst >> 6) & 0b0001_1111) as u8;
            let funct = (inst & 0b0011_1111) as u8;

            Instruction::R(rs, rt, rd, shift, funct)
        }

        // Jump instructions
        JMP => {
            let addr = (inst & 0b0000_0011__1111_1111__1111_1111__1111_1111) << 2;

            // Transmute the address (which is a u32) into a signed number
            unsafe {
                let addr = transmute::<u32, i32>(addr);
                Instruction::J(addr)
            }
        }

        // Otherwise assume it's an immediate
        OP_ORI => {
            let rs = ((inst >> 21) & 0b0001_1111) as u8;
            let rt = ((inst >> 16) & 0b0001_1111) as u8;
            let imm = inst & 0xff_ff;
            Instruction::I(OP_ORI, rs, rt, imm)
        }

        OP_ADDI => {
            let rs = ((inst >> 21) & 0b0001_1111) as u8;
            let rt = ((inst >> 16) & 0b0001_1111) as u8;
            let imm = inst & 0xff_ff;
            Instruction::I(OP_ADDI, rs, rt, imm)

        }

        // Otherwise it's invalid
        _ => Instruction::Invalid,
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use helpers;
    use constants::*;

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
        let inst = 0x03_ff_ff_ff;
        println!("{:#b}", inst);
        let got = parse_instruction(inst);
        let should_be = Instruction::R(31, 31, 31, 31, 63);
        println!("{:?}", got);
        assert_eq!(got, should_be);

        let mut inst = 0b00;
        // let opcode = 0b0011_1111 << 26;  // 63
        let rs = 0b0001_1010 << 21;  // 26
        let rt = 0b0000_0100 << 16;  // 4
        let rd = 0b0001_1111 << 11;  // 31
        let shift = 0b0001_1101 << 6;  // 29
        let funct = 0b0000_1011;  // 11

        inst |= rs | rt | rd | shift | funct;

        // Double check we composed the instruction right
        assert_eq!(inst, 0b000000_11010_00100_11111_11101_001011);

        let got = parse_instruction(inst);
        let should_be = Instruction::R(26, 4, 31, 29, 11);
        println!("{:?}", got);
        assert_eq!(got, should_be);
    }

    #[test]
    fn parse_jump_instruction() {
        // Create a valid jump instruction
        let offset: i32 = 128;
        let inst = helpers::jump_instruction(offset);
        let got = parse_instruction(inst);
        let should_be = Instruction::J(offset);
        assert_eq!(got, should_be);
    }

    #[test]
    fn parse_syscall_instruction() {
        let inst = 12;
        let got = parse_instruction(inst);
        let should_be = Instruction::Syscall;
        assert_eq!(got, should_be);
    }

    #[test]
    fn parse_i_instruction() {
        let inst = helpers::make_i_instruction(OP_ORI as usize, TEMP_1, TEMP_0, 42);
        let got = parse_instruction(inst);
        let should_be = Instruction::I(OP_ORI, TEMP_1 as u8, TEMP_0 as u8, 42);
        assert_eq!(got, should_be);
    }

    #[test]
    fn parse_invalid_instruction() {
        let mut inst = 0x00;
        let opcode = 0b0011_1111 << 26;  // 63
        inst |= opcode;
        let got = parse_instruction(inst);
        let should_be = Instruction::Invalid;
        assert_eq!(got, should_be);
    }

    #[test]
    fn step_one_syscall_instruction() {
        // Create a program consisting of a single add
        let inst = helpers::syscall_instruction();
        let instructions = helpers::instructions_to_bytes(vec![inst]);

        // then load it
        let mut cpu = Processor::new();
        cpu.load(instructions).unwrap();

        // Make sure to put a valid syscall code into the $v0 register
        // (in this case we're using the exit call
        cpu.registers[RET_1] = 10;

        assert!(!cpu.stopped);

        // step 2: Actually run the instruction
        cpu.step().unwrap();

        // Then make sure the syscall was applied
        assert!(cpu.stopped);
    }

    #[test]
    fn step_one_add_instruction() {
        // Create a program consisting of a single add
        let inst = helpers::add_instruction(TEMP_0, TEMP_0, TEMP_1);  // add r1, r1, r2
        let instructions = vec![inst];
        let instructions_as_bytes = helpers::instructions_to_bytes(instructions);

        // then load it
        let mut cpu = Processor::new();
        cpu.load(instructions_as_bytes).unwrap();

        // step 1: Put something interesting in registers 1 and 2
        cpu.registers[TEMP_0] = 1;
        cpu.registers[TEMP_1] = 1;

        // step 2: Actually run the instruction
        cpu.step().unwrap();

        // step 3: Check that 1 + 1 = 2
        assert_eq!(cpu.registers[TEMP_0], 2);

        // step 4: Profit!!!
    }

    #[test]
    fn step_one_jump_instruction() {
        let offset = 0b0011_1100;
        let inst = helpers::jump_instruction(offset);  // j 0xffff
        let instructions = helpers::instructions_to_bytes(vec![inst]);

        let mut cpu = Processor::new();

        // Set the pc to something other than zero
        cpu.pc = 42;

        // Then load the instructions there
        for (i, byte) in instructions.iter().enumerate() {
            cpu.memory[cpu.pc + i] = *byte;
        }

        cpu.step().unwrap();
        assert_eq!(cpu.pc as u32, 42 + offset as u32);
    }

    #[test]
    fn noop_stops_execution() {
        let mut cpu = Processor::new();
        assert_eq!(cpu.memory[cpu.pc], 0);
        cpu.step().unwrap();
        assert!(cpu.stopped);
    }

    #[test]
    fn start_addition_program_and_error_when_end_reached() {
        let instructions = vec![
            helpers::add_instruction(TEMP_0, TEMP_0, TEMP_1),  // add r1, r1, r2
            helpers::syscall_instruction(),
        ];
        let instructions = helpers::instructions_to_bytes(instructions);

        let mut cpu = Processor::new();
        cpu.load(instructions).unwrap();

        cpu.registers[TEMP_0] = 4;
        cpu.registers[TEMP_1] = 38;

        let result = cpu.start();

        assert!(result.is_err());
        assert_eq!(cpu.registers[TEMP_0], 42);
    }

    // Put tests for each individual R instruction in its own sub
    // module so they're all together
    mod r_instructions {
        use super::super::*;
        use constants::*;

        #[test]
        fn execute_single_r_add_instruction() {
            let mut cpu = Processor::new();

            // Put something interesting in registers 1 and 2
            cpu.registers[TEMP_0] = 42;
            cpu.registers[TEMP_1] = 7;

            // Run the instruction r1 = r1+r2
            cpu.handle_r_instruction(TEMP_0 as u8, TEMP_0 as u8, TEMP_1 as u8, 0, FUNCT_ADD)
                .unwrap();

            // Check the addition was correct
            assert_eq!(cpu.registers[TEMP_0], 49);
        }

        #[test]
        fn execute_single_r_and_instruction() {
            let mut cpu = Processor::new();
            cpu.registers[TEMP_0] = 42;
            cpu.registers[TEMP_1] = 7;
            cpu.handle_r_instruction(TEMP_0 as u8, TEMP_0 as u8, TEMP_1 as u8, 0, FUNCT_AND)
                .unwrap();
            assert_eq!(cpu.registers[TEMP_0], 42 & 7);
        }

        #[test]
        fn execute_single_r_mult_instruction() {
            let mut cpu = Processor::new();
            cpu.registers[TEMP_0] = 42;
            cpu.registers[TEMP_1] = 7;
            cpu.handle_r_instruction(TEMP_0 as u8, TEMP_0 as u8, TEMP_1 as u8, 0, FUNCT_MULT)
                .unwrap();
            assert_eq!(cpu.registers[TEMP_0], 42 * 7);
        }

        #[test]
        fn execute_single_r_div_instruction() {
            let mut cpu = Processor::new();
            cpu.registers[TEMP_0] = 43;
            cpu.registers[TEMP_1] = 7;
            cpu.handle_r_instruction(TEMP_0 as u8, TEMP_0 as u8, TEMP_1 as u8, 0, FUNCT_DIV)
                .unwrap();

            // Note: this is integer division
            assert_eq!(cpu.registers[TEMP_0], 6);
        }
    }


    /// Package all tests for basic syscalls into their own module, similar
    /// to what's done with the R instructions
    mod syscalls {
        use super::super::*;
        use constants::*;

        #[test]
        #[should_panic]
        fn syscall_with_invalid_code_fails() {
            let mut cpu = Processor::new();
            cpu.handle_syscall(123).unwrap();
        }

        #[test]
        fn exit() {
            let mut cpu = Processor::new();
            assert_eq!(cpu.stopped, false);
            cpu.handle_syscall(10).unwrap();
            assert_eq!(cpu.stopped, true);
        }

        #[test]
        fn print_integer() {
            let mut cpu = Processor::new();
            cpu.registers[ARG_0] = 42;
            cpu.handle_syscall(1).unwrap();
        }
    }
}
