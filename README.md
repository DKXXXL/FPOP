# FPOP, Family Polymorphism for Proof Assistant, a Prototype.


# Build Instruction

We need to pins to
1. Ocaml base compiler to  4.13.1
2. coq to 8.15.0, 

## Build Source Code

directly run
```Bash
dune build
```

## Run all the showcase commands from the guide
We have pack all the coqc commnds into testshowcase.sh in FPOP directory. 

The following commands are run under the `FPOP` directory

We warn that, these tests are time consuming

```Bash
cd FPOP
cat testshowcase.sh
```
The reader can directly try to run them via this shell file, and check output*.txt for the dump info.

Currently we cannot turn off the debug dump.



***

# Directory Structure
1. `showcase_test/` includes all the showcase included in the paper 
2. `src/` and `theories/` includes all the source code of our plugin. `LibTactics.v` and `Maps.v` are directly from Software Foundation
## about `src` directory
1. `src/familytype.ml` contains the main functionality of our plugin. For example, the internal data structure (representing family) and the translation from this internal data structure to Coq's command.
2.  `src/fampoly.mlg` is the mlg file extending the Vernacular syntax for our plugin
3.  `src/famprogram.ml` mainly interacts with the user. It contains the function that `fampoly.mlg` will invoke
4. `src/fenv.ml` handles the environment/definitions of the families in our internal structure
5. `src/finduction.ml` implements the `FRecursion` facility
6.  `src/finh.ml` implements the inheritance facility
7.  `src/ftheorem.ml` makes it possible to use proof script to work with our plugin
8.  `src/utils` and `src/CCCache.ml` are helpers. `CCCache.ml` is directly copied from `OCaml-containers` (Thanks Simon Cruanes!)


***

# Known Bugs
1. The debug dump will be generated during the usage of our plugin. We currently doesn't support turning it off
2. Families have to be wrapped inside one module. (i.e. There has to be a very top level module, then we can define family inside this module)

# Known Bugs on MacOS
1. When running `coqc` on two `Analysis_showcase`, it might took around 3 times the expected time. It won't immediately terminate after the final command `Print Analysis_showcase.LangCP`.
2. VSCoq on MacOS is not working well with our plugin


***

## Artifact Avaliable at 
https://doi.org/10.5281/zenodo.7800226

