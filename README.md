# c0-boole
This is a C0 frontend for CSLib's Boole, which is an intermediary verification language written in / for Lean4. C0 is a safer subset of C developed at CMU and is used by the entire computer science undergraduate cohort to teach foundational data structures, algorithms, and imperative programming. There is an emphasis placed on safety and code reasoning, and thus translates nicely to the Boole IVL. 

# LLVM
To aid with the development of the [C0 frontend](https://github.com/chrissuu/c0-boole) for the Boole IVL (and due to no official C0 compiler), the ```llvm``` branch houses the code for compiling C0 programs to the LLVM IR. The compiler itself is written in Lean such that we can prove interesting correctness properties (for instance, AST elaboration preserving the semantics of the original code).
