//! A MIPS emulator written entirely in Rust.

#![warn(missing_docs)]
#![feature(plugin)]
#![plugin(docopt_macros)]

extern crate byteorder;
extern crate rustc_serialize;
extern crate docopt;

pub mod processor;
mod constants;
pub mod helpers;

use std::fs::File;
use std::io::Read;
use std::process::exit;

pub use processor::{Instruction, Processor, parse_instruction};


docopt!(Args derive Debug, "
A MIPS emulator written in Rust.

Usage:
    mips [options] <file>
    mips (-h | --help)
    mips --version

Options:
    --version        Print the version number and exit
    -h --help        Print this help text
    -v --verbose     Verbose output
");

fn main() {
    let args: Args = Args::docopt().decode().unwrap_or_else(|e| e.exit());

    if args.flag_version {
        println!("{} v{}", "mips", env!("CARGO_PKG_VERSION"));
    } else if !args.arg_file.is_empty() {
        run_program(args.arg_file.clone(), args);
    }

    exit(0);
}


/// Read in a filename, load it into the emulator's memory, and then step
/// through instructions until the program either terminates or crashes.
fn run_program(filename: String, args: Args) -> u32 {
    let mut data: Vec<u8> = Vec::new();
    let mut f = File::open(&filename).expect("Unable to open file");
    f.read_to_end(&mut data).expect("Unable to read data");

    if args.flag_verbose {
        println!("Read {:#} bytes from {}", data.len(), filename);
    }

    // Create a new processor
    let mut cpu = processor::Processor::new();

    // For the test, put 1 in registers 1 and 2, then print the
    // contents of the registers for the user
    cpu.registers[1] = 1;
    cpu.registers[2] = 1;
    println!("{:?}", cpu.registers);

    // And load the program into memory
    match cpu.load(data) {
        Ok(_) => {
            if args.flag_verbose {
                println!("Program loaded");
            }
        },
        Err(e) => {
            println!("ERROR: {}", e);
            return 1;
        }
    }

    // Now keep executing instructions until we hit an error
    loop {
        let result = cpu.step();
        match result {
            Err(e) => {
                println!("ERROR: {}", e);
                break
            },
            Ok(()) => {},
        }
    }

    // Print the contents of the registers and the program counter
    if args.flag_verbose {
        println!("Program Counter: {}", cpu.program_counter()-4);
        println!("{:?}", cpu.registers);
    }

    0
}
