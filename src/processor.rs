

/// The registers used, and their common names, are as follows:
///
/// Number         Name           Comments
/// ======         ====           ========
/// $0             $zero          Always zero
/// $1             $at            Reserved for assembler
/// $2, $3         $v0, $v1       First and second return values, respectively
/// $4, ..., $7    $a0, ..., $a3  First four arguments to functions
/// $8, ..., $15   $t0, ..., $t7  Temporary registers
/// $16, ..., $23  $s0, ..., $s7  Saved registers
/// $24, $25       $t8, $t9       More temporary registers
/// $26, $27       $k0, $k1       Reserved for kernel (operating system)
/// $28            $gp            Global pointer
/// $29            $sp            Stack pointer
/// $30            $fp            Frame pointer
/// $31            $ra            Return address

#[derive(Default)]
#[allow(dead_code)]
pub struct Processor {
    memory: Vec<u8>,

    zero: u32,
    at: u32,
    return_values: [u32; 2],

}


impl Processor {
    pub fn new(program: Vec<u8>) -> Result<Processor, String> {
        let mut vm = Processor::default();
        try!(vm.load(program));
        Ok(vm)
    }

    pub fn load(&mut self, program: Vec<u8>) -> Result<(), String> {
        unimplemented!()
    }
}
