A Basic MIPS Emulator
=====================

The plan is to build a MIPS emulator that roughly follows [this][1] assignment
brief I found on the internet.


Useful References
-----------------

- A MIPS simulator written in Python ([github][2])


To-Do List
----------

- [x] Create a basic processor to represent registers and memory
- [x] Parse and execute a single R instruction
- [ ] Parse and execute a single I instruction
- [ ] Write an assembler that'll turn MIPS assembly code into machine code
      (binary)
- [x] Implement jump instructions
- [ ] Add syscalls
- [ ] Compile then execute some of the basic programs in the `/src/test`
      directory
- [ ] Implement a `GDB` like stepper mechanism
- [ ] Pass the `torture.s` test program


[1]: http://web.stanford.edu/class/ee182/Projects/PA2/pa2.html
[2]: https://github.com/maguire/MIPS-Simulator
