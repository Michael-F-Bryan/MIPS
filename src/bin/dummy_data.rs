extern crate mips;

use mips::helpers;
use mips::constants::*;
use std::fs::File;
use std::io::Write;


fn dummy_data() -> Vec<u8> {
    let instructions = vec![
        helpers::make_i_instruction(OP_ORI as usize, TEMP_0, 0, 42), // Put 42 into $t1
        helpers::make_i_instruction(OP_ORI as usize, TEMP_1, 0, 7), // Put 7 into $t2
        helpers::add_instruction(TEMP_0 as usize, TEMP_0, TEMP_1), // $t1 = $t1 + $t2

        // Put 1 into $v0 for the syscall
        helpers::make_i_instruction(OP_ORI as usize, RET_1 as usize, 0, 1),

        // Move TEMP_1 to the ARG_0 register so the print syscall can use it
        helpers::make_i_instruction(OP_ORI as usize, ARG_0, TEMP_0, 0),
        helpers::syscall_instruction(),
    ];
    helpers::instructions_to_bytes(instructions)
}


fn main() {
    let binary = dummy_data();
    let mut f = File::create("add").unwrap();
    f.write(&binary).unwrap();
}
