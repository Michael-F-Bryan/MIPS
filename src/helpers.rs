//! A module full of useful miscellaneous functions that help automate
//! boring jobs like creating the machine code representation of an
//! instruction.


/// A simple helper that creates an add instruction.
///
/// Converts something like `add r4,r2,r4` into its corresponding
/// machine code instruction.
pub fn add_instruction(rd: usize, rs: usize, rt: usize) -> u32 {
    make_r_instruction(0, rs, rt, rd, 0, 0b100000)
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

    let inst = (0
            | opcode << 26
            | rs << 21
            | rt << 16
            | rd << 11
            | shift << 6
            | funct);

    inst as u32
}


#[cfg(test)]
mod test {
    use super::*;

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
}
