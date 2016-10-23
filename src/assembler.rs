//! An assembler that parses a program written in MIPS assembly code and
//! translates it to machine code.

use processor::Instruction;
use std::fmt::{Formatter, Error, Debug};


/// A parser which acts as an iterator over instructions.
#[derive(PartialEq)]
pub struct Parser {
    source: String,
    pointer: u32,
    line: u32,
}

impl Debug for Parser {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "Parser(pointer={}, line={})", self.pointer, self.line)
    }
}


impl Parser {
    /// Create a new Parser from source code.
    pub fn new(src: String) -> Parser {
        Parser {
            source: src,
            pointer: 0,
            line: 0,
        }
    }
}

impl Iterator for Parser {
    type Item = Instruction;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}


#[cfg(test)]
mod test {
    use super::*;
    // use processor::Instruction;

    #[test]
    fn constructor() {
        let src = String::new();
        let got = Parser::new(src.clone());
        let should_be = Parser {
            source: src,
            pointer: 0,
            line: 0,
        };
        assert_eq!(got, should_be);
    }

    #[test]
    fn get_first_instruction() {
        let src = "add $r1, $r2, $r3";
        let mut parser = Parser::new(src.to_string());
        let got = parser.next();
        // let should_be = Instruction::R();
        // assert_eq!(got, Some(should_be));
    }

    #[test]
    fn dummy() {
        assert!("a" == "hello");
    }
}
