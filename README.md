# Gong

## Liveness and Safety checker for MiGo types

## Prerequisites

- ghc version 7.10.3+

### Required CABAL packages

- ansi-terminal
- unbound
- cmdargs
- parsec

For Ubuntu Linux, `ghc` can be installed via `apt-get` as part of
[**Haskell Platform**](https://www.haskell.org/platform/), and the haskell
packages can be installed via [**cabal**](https://www.haskell.org/cabal/).

    $ sudo apt-get install haskell-platform

Then use cabal to install the required haskell packages:

    $ cabal install ansi-terminal unbound cmdargs parsec

Finally, verify that `ghc` version is at least 7.10.3:

    $ ghc --version
    The Glorious Glasgow Haskell Compilation System, version 7.10.3

## Install

To build and install `Gong`, first download or checkout the source code:

    $ git clone https://github.com/nickng/gong.git

Then build using the following command:

    $ cd gong; ghc Gong.hs

## Running

To verify a given input `.migo` file, use the following command, which will
output the result in the standard output:

    $ ./Gong -A path/to/file.migo
    Bound (k): 2
    Number of k-states: 4
    Liveness: True
    Safety: True

To see all options available, use the `--help` flag.

    $ ./Gong --help

Some further example `.migo` files are available under the `examples/`
directory.
