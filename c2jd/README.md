A program for translating C headers into Jackdaw code

## Usage

Requires a c compiler installed which supports running the preprocessor only (cpp command)

* Create a C source file which includes the header files
* Run c2jd: `c2jd headers.c > headers.jackdaw`
* The jackdaw file is written to stdout; any definitions which couldn't be translated are marked with a code comment
