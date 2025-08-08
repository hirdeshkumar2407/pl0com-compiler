# pl0com: Toy Compiler for Code Optimization and Transformation

**Author:** Hirdesh Kumar  
**Date:** 2025  
**Course:** Code Optimization and Transformation — Politecnico di Milano

---

## Overview

**pl0com** is a toy compiler developed as part of the *Code Optimization and Transformation* course at Politecnico di Milano. It fills the gap between minimal academic compilers (like ACSE) and production-grade compilers such as Clang or GCC.

Written in Python, pl0com features:

- A hand-written recursive-descent parser (no Yacc/Bison)
- An Abstract Syntax Tree (AST) and Intermediate Representation (IR)
- ARMv6 assembly code generation targeting real hardware (original Raspberry Pi)
- Initial loop optimizations like **loop unrolling** and **strip mining**
- Register allocation and runtime support in C

---

## Highlights & Recent Progress

- **Loop Unrolling:** Implemented multiple versions of loop unrolling to optimize execution.
- **Strip Mining:** Added strip mining techniques for loop optimization.
- **For-Loop Support:** Completed parsing and codegen for `for` loops.
- **Register Allocation:** Developed ARM register allocator to improve performance.
- **Debugging:** Enabled QEMU and GDB multi-architecture debugging support.
- Continuous improvements and bug fixes as seen in commit history (Apr-May 2025).

---

## Getting Started

### Prerequisites

On Ubuntu/Linux, install dependencies:

```bash
su

do apt update

```

### Build and Run
Compile source code (edit or add your program at the end of lexer.py):
```bash
./main.py out.s
```

sudo apt install qemu-user gcc-arm-linux-gnueabi gdb-multiarch
