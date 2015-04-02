#Protoplasm

A simple compiler developed for a Compiler course. The language frontend is
pretty simple, but the IR is feature complete.

This compiler uses a SSA IR, with the exception of memory access. Code generation is done in-house, without any dependencies like LLVM. For now the only target supported is MIPS.
