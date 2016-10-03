//! A MIPS emulator written entirely in Rust.

#![warn(missing_docs)]
#![feature(plugin)]
#![plugin(docopt_macros)]

extern crate byteorder;
extern crate rustc_serialize;
extern crate docopt;
#[macro_use]
extern crate log;
extern crate env_logger;

extern crate mips;

use mips::Processor;

use std::fs::File;
use std::io::Read;
use std::process::exit;


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
    env_logger::init().unwrap();

    debug!("Command Line Arguments -> {:?}", args);

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
        info!("Read {:#} bytes from {}", data.len(), filename);
    }

    // Create a new processor
    let mut cpu = Processor::new();

    // And load the program into memory
    match cpu.load(data) {
        Ok(_) => {
            if args.flag_verbose {
                info!("Program loaded");
            }
        }
        Err(e) => {
            error!("{}", e);
            return 1;
        }
    }

    // Now keep executing instructions until we hit an error
    let result = cpu.start();
    if result.is_err() {
        error!("{}", result.unwrap_err());
    }

    // Print the contents of the registers and the program counter
    if args.flag_verbose {
        println!("Program Counter: {}", cpu.program_counter() - 4);
        println!("{:?}", cpu.registers);
    }

    0
}
