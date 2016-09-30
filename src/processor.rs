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
//! $16, ..., $23  $s0, ..., $s7  Saved registers
//! $24, $25       $t8, $t9       More temporary registers
//! $26, $27       $k0, $k1       Reserved for kernel (operating system)
//! $28            $gp            Global pointer
//! $29            $sp            Stack pointer
//! $30            $fp            Frame pointer
//! $31            $ra            Return address


// Define some constants to make accessing the individual registers easier
const zero: usize = 0;
const ret_1: usize = 2;
const ret_2: usize = 3;
const global_pointer: usize = 28;
const stack_pointer: usize = 29;
const frame_pointer: usize = 30;
const return_address: usize = 31;


#[allow(dead_code)]
pub struct Processor {
    /// Store RAM as a big array of bytes (2^16).
    memory: [u8; 65536],

    /// The 32 registers
    registers: [u32; 32],

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

        // Otherwise, copy the program in element-wise
        for (i, code) in program.into_iter().enumerate() {
            self.memory[i] = code;
        }
        Ok(num_bytes)
    }
}

impl Default for Processor {
    fn default() -> Processor {
        Processor { memory: [0; 65536],
                    registers: [0; 32]
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
