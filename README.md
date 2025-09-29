A borrow-checked applications/systems language taking ideas from Rust, C++ and Zig.

The borrow checking in this language is simpler than in Rust as it does not support first-class references,
i.e. references are not types and cannot be stored in variables or fields.
Instead of functions taking and returning reference types,
there are 'accessor functions' which return a reference to the first parameter.

Generics work similarly to C++'s templates and Zig's compile-time and there are no macros.

To see what the language looks like, browse through the standard library code in jackdawc/res/stlib.

## Compiler development environment setup (Linux)

These instructions include creating a Distrobox container which is optional.

If a container is used then the IDE (VSCode/VSCodium) must be installed within the container.


`distrobox create --image debian:11-slim --name dev --home $HOME/dev`

`distrobox enter dev`

`sudo dnf install make git gcc build-essential curl libffi-dev libffi7 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5 pkg-config`

Install GHCup from https://www.haskell.org/ghcup/

`curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh`

Pick the default for all options and don't install HLS if using VSCodium/VSCode as the extension will download the correct version

GHC version should be 9.6.7

If happy_info.sh is to be used then run `cabal install happy` and check that `$HOME/.local/bin` is on the `$PATH`

Install VSCodium/VSCode .deb/.rpm and the Haskell extension
* https://open-vsx.org/extension/haskell/haskell
* https://marketplace.visualstudio.com/items?itemName=haskell.haskell

Open the project and press 'yes' when it asks to download HLS

If the language server leaks memory (and freezes the computer) then search the VSCodium/VSCode settings for 
'plugin global on' and disable all except: 
* Ghcide-completions
* Ghcide-code-actions-imports-exports

Installing something like EarlyOOM also helps, as does disabling and reenabling the Haskell extension when memory usage starts to climb.


## Debugging
Jackdaw code can be debugged with GDB/LLDB. Enable `debug.allowBreakpointsEverywhere` in VSCodium/VSCode.

Ignore local variables beginning with 'x', Jackdaw variables begin with 'v'.

The debugging experience will improve once an LLVM backend is added to the compiler.

## Licence

Copyright (c) 2025 "VoxelMagpie"

This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.

The MPL-2.0 licence applies to every file, regardless of whether it has a licence header or not.

The MPL-2.0 is similar to the LGPL but without the need for dynamic linking. 

This means that any changes made to the code must be shared
but the code can be used within a proprietary/GPL/MIT/etc. codebase. 


## Haskell resources

* What I Wish I Knew When Learning Haskell: <https://sdiehl.github.io/wiwinwlh>
* Haskell wikibook: <https://en.wikibooks.org/wiki/Haskell>


