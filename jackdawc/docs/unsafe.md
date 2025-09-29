* Do not violate aliasing guarantees (C restrict keyword) for reference parameters
    * This applies to shared references as well
    * There must be no way a function could unintentionally modify a value that it references, except through the (exclusive) reference to that value
* Raw pointers disable move semantics
    * This can be used to prevent drop functions being run, e.g.:
        * `(&x).* = y;` Does not drop x, does move y
        * `x = (&y).*;` Drops x, copies the bytes of y
* C function declarations should usually be marked @Unsafe @NoThrow
* Accessor functions can return raw pointers (or RawSlice)
* Basic exception safety
    * Do not allow data/pointers to become invalid when an exception is thrown
    * E.g. leaking memory in raw pointers, leaving an object in an invalid state so it cannot be safely dropped 