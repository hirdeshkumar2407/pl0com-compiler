# pl0com: A Python-Based Compiler for ARMv6 with Loop Optimizations

## 🎯 Project Mission & Context
Developed for the "Code Optimization and Transformation" course at Politecnico di Milano, pl0com is an educational compiler designed to bridge the gap between minimalist academic examples and the complexity of production compilers like GCC or Clang. This project was a deep dive into the art and science of turning high-level code into efficient, low-level machine instructions.

## ✨ Core Features & Architecture
- pl0com is a complete compiler pipeline, written from scratch in Python, demonstrating a first-principles understanding of compiler design.
- Hand-Written Recursive-Descent Parser: Full parsing of the language without relying on external tools like Yacc or Bison.
- Intermediate Representations: Builds a clean Abstract Syntax Tree (AST) and a flexible Intermediate Representation (IR) to facilitate optimizations.
- ARMv6 Code Generation: Targets real-world hardware (the original Raspberry Pi), generating functional ARM assembly.
- Advanced Loop Optimizations: Implemented key performance-enhancing techniques, including:
-- Loop Unrolling: Multiple versions to reduce loop overhead.
-- Strip Mining: To improve cache performance and data locality.
-- Professional Tooling: Includes a robust register allocator for ARM and is fully enabled for debugging with QEMU and GDB multi-architecture support.

## 🛠️ Getting Started
Prerequisites (Ubuntu/Debian):
 

```
Bash
sudo apt-get update && sudo apt-get install qemu-user gcc-arm-linux-gnueabi gdb-multiarch
```
Build & Run:
The compiler takes a source file and produces an assembly file.
c
# Example: Compile your_program.pl0 to out.s
```
./main.py your_program.pl0 out.s
```
