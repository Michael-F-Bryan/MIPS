A Basic MIPS Emulator
=====================

The plan is to build a MIPS emulator that roughly follows [this][1] assignment
brief I found on the internet.

Note that you'll probably want to use the `nightly` version of the rust
compiler. Check out [rustup.rs][rustup] for an easy way to manage rust
versions.

Usage
-----

This library comes with a couple useful executables for emulating MIPS programs.

One of these executables is called `dummy_data`, and will create a dummy
executable at the specified location. This is helpful for testing the emulator
out on real binaries.

At the moment `dummy_data` produces something similar to this:

    ori $t1, $0, 42  ;  $t1 = 42
    ori $t2, $0, 7  ;  $t2 = 7
    add $t1, $t1, $t2  ; $t1 = $t1 + $t2
    print($t1)

The second executable is the emulator itself. To run an executable, simply
do:

    mips_emulator /path/to/executable


To-Do List
----------

- [x] Create a basic processor to represent registers and memory
- [x] Parse and execute a single R instruction
- [x] Parse and execute a single I instruction
- [ ] Write an assembler that'll turn MIPS assembly code into machine code
      (binary)
- [x] Implement jump instructions
- [x] Add syscalls
- [ ] Compile then execute some of the basic programs in the `/src/test`
      directory
- [x] Add a basic command line interface
- [ ] Implement a `GDB` like stepper mechanism
- [ ] Pass the `torture.s` test program


[1]: http://web.stanford.edu/class/ee182/Projects/PA2/pa2.html
[2]: https://github.com/maguire/MIPS-Simulator
[rustup]: https://www.rustup.rs/
