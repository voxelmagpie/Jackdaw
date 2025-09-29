* Lexing: Src -> Vec Tokens
* Parsing: Vec Tokens -> AST
    * Keywords and operators are defined here
* Type checking, name lookup, borrow checking: AST -> TCIR -> HIR
    * Global names are in the form `@package-name/dir_name/file_name:TypeName.name`
    * Local names are given integer IDs
    * All non-generic code and all generic code accessed (indirectly) from the start function are type checked
    * Borrow checker is a subpass of the type checking pass and runs per-function
    * TAST is is not gathered for the entire program
        * Discarded after borrow checking each function
* Lowering: HIR -> LIR
    * Type checker is run again for genericd functions
* C Transpiling: LIR -> C
* Machine code generation & linking (GCC/Clang)


