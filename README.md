# pl0com

Toy compiler for the Code Optimization and Transformation course held at
Politecnico di Milano.

This compiler can be considered the middle point between ACSE and a serious
compiler like clang or GCC ~~(apart from the fact that it is written in a
ridiculously inappropriate language for the task such as Python)~~.

It features a hand-written recursive-descent parser (instead of a Yacc+Bison
generated parser), an AST and an IR (instead of simply using syntax-directed
translation to a simplified flavour of machine language), and a code
generation stage which produces (hopefully) valid ARM code (instead of producing
code for a fictional architecture, albeit there are rumors that a version of
ACSE modified to produce x86_64 code exists somewhere ::hint hint::).

What is still missing is support for any kind of optimization, and additionally
the AST and IR design leaves a lot to be desired. The usage of real memory
variables -- instead of always placing them into registers like in ACSE --
actually makes this compiler produce much worse code than ACSE, but what can
you do. After all, this issue could only be fixed by rewriting the whole
compiler, and perfect is the worst enemy of good. Leave it be, and bring your
search of perfection elsewhere ~~and far away from Python please~~.

## How to test the output

If you are running Linux, and your PC doesn't have an ARM CPU, an easy way to
run a usermode Linux binary built for ARM is to use QEmu usermode emulation
(https://qemu-project.gitlab.io/qemu/user/main.html#linux-user-space-emulator).

These are the steps to follow to properly compile, run and debug a program
compiled by `pl0com` on a Ubuntu Linux machine. Of course you will have to
adapt some commands to your specific distribution if you are not using Ubuntu.
At the time I am writing Ubuntu is the most prolific distribution there is,
so don't complain if you are reading this in a distant future where everybody
uses Arch (and in that case God may have mercy on your soul).

#### Step 1: Install usermode QEmu, ARM GCC and GDB.

Simply run the following command:

```sh
$ sudo apt qemu-user gcc-arm-linux-gnueabi gdb-multiarch
```

Note that there is another GCC package named `gcc-arm-linux-gnueabihf`. The
`hf` at the end stands for "hard float" AKA the VFP floating point extension
of ARM. However this extension does not exist in ARMv6 which is the version
of the ARM instruction set used by `pl0com`, thus using the GCC installed by
that package causes troubles.

The ARMv6 choice was made because that was the instruction set implemented on
the original Raspberry Pi, so it ensures a wide level of compatibility in case
you want to run the compiled code on real hardware.

#### Step 2: Compile a program with `pl0com`

First, place the program to be compiled at the end of `lexer.py` unless you
are happy with the shitty test program that is already there. Note that such
shitty test program is the only program the compiler is guaranteed to
be able to compile correctly.

Then, produce an assembly file from the compiler by invoking it:

```sh
$ ./main.py out.s
```

#### Step 3: Link the program with the runtime library

```sh
$ arm-linux-gnueabi-gcc out.s runtime.c -g -static -march=armv6 -o out
```

Apart from the `-g` argument which you should know what it is (and if you don't
you should be ashamed of yourself), the `-static` argument forces GCC to link
everything statically (libc and syscall stubs included), and `-march=armv6`
selects the ARMv6 architecture.

#### Step 4: Run the binary

```sh
qemu-arm -cpu arm1136 out
```

The `-cpu arm1136` argument can be omitted, it only specifies which CPU core to
emulate. The ARM1136 is the oldest core supported by QEmu that implements ARMv6
(and in fact it does not implement anything more than that).

#### Step 4a: Debug the binary

In order to attach GDB to the binary being run, the qemu invocation changes like
this:

```sh
qemu-arm -cpu arm1136 -g 7777
```

The `-g 7777` argument tells QEmu to wait GDB to connect via a socket on port
`7777`. Of course the socket port can be changed to any number you like as long
as it does not clash with standard sockets. In general, the larger the number,
the least probable are the clashes.

In a separate terminal, invoke `gdb-multiarch` (NOT normal `gdb`, that just
supports your native architecture).

At the GDB prompt run the following commands:

```
file out
target remote :7777
```

The command `file out` tells GDB the executable from where it should load
symbolication and debugging information from.

The command `target remote :7777` actually connects GDB to QEmu. You can
also debug another machine over the network by specifying an IP address before
the port number and the colon (of course; what did you think the colon was
there for?).

At this point you can type `continue` to un-freeze QEmu and actually start
the execution of the program. Everything works as if you were debugging a
native process (of course the disassembly will be in ARM assembly language),
except for the fact that the command `run` will not work.

### What if I am not using Linux?

Create a virtual machine running Linux and then run the steps above.
Seriously.

Alternatively, if you want to limit the amount of recursion (albeit as a
computer scientist the sole mention of recursion should be enough to produce an
above-average level of excitement) you can use QEmu in system mode to setup a
native ARMv6 VM (you can pilfer Raspbian binaries for that purpose).
Good luck with file sharing.
