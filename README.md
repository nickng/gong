# Gong

## Liveness and Safety checker for MiGo types

[![Build Status](https://travis-ci.org/nickng/gong.svg?branch=master)](https://travis-ci.org/nickng/gong)

## Prerequisites

- ghc version 7.10.3+
- cabal

For Ubuntu Linux, `ghc` can be installed via `apt-get` as part of
[**Haskell Platform**](https://www.haskell.org/platform/), and the 
packages can be installed via [**cabal**](https://www.haskell.org/cabal/).

    $ sudo apt-get install haskell-platform

Then run cabal update:

    $ cabal update

Finally, verify that `ghc` version is at least 7.10.1, for example:

    $ ghc --version
    The Glorious Glasgow Haskell Compilation System, version 7.10.3

## Install

To build and install `Gong`, first download or checkout the source code:

    $ git clone https://github.com/nickng/gong.git

Then build using the following command:

    $ cd gong; cabal install

The built Gong binary can be found in `dist/build/Gong`, use the following to
add to your current `$PATH`:

    $ export PATH=$(pwd)/dist/build/Gong:$PATH

## Running

To verify a given input `.migo` file, use the following command, which will
output the result in the standard output:

    $ Gong -A path/to/file.migo
    Bound (k): 2
    Number of k-states: 4
    Liveness: True
    Safety: True

To see all options available, use the `--help` flag.

    $ Gong --help

Some further example `.migo` files are available under the `examples/`
directory.
