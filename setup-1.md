# Source Code Building FPOP for coqc verification

The reader can skip if they know 

## Opam Installation

```bash
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
```

make sure all the dependencies are ready before initializing opam
otherwise `opam init` will go to error

On Ubunbute, dependencies should at least include, `make`, a c compiler , `bwrap` or bubblewrap, and `patch`.

We also need `bzip2` when installing `utop` later

For different OS, the dependencies might be a little different. We request the audience to search for the correct way to run `opam init` on their machine (and of course the `utop`-requiring `bzip2`)


```bash
opam init
```
## Opam Setup 
We need to pins to
1. Ocaml base compiler to 
2. coq to 8.15.0, 
3. utop to 2.11.0

So for each of the next section, we will pin accordingly.

### We first switch to OCaml compiler 4.13.1

```Bash
opam switch create 4.13.1
opam switch 4.13.1
eval $(opam env)
```

### Then pins Coq

```Bash
opam pin add coq 8.15.0
```

### Then pins utop 

```Bash
opam pin add utop 2.11.0
```

## Build Source Code

After unzipping `FPOP.zip`, the reader should only see `FPOP` directory there

Go into FPOP directory, 
```Bash
cd FPOP
dune build
```

## Run all the showcase commands from the guide
We have pack all the coqc commnds into testshowcase.sh in FPOP directory. 

The following commands are run under the `FPOP` directory

```Bash
cd FPOP
cat testshowcase.sh
```
The reader can directly try to run them via this shell file, and check output*.txt

But don't forgot to create `testoutput` directory under `FPOP` directory first! Otherwise extraction will fail.

```Bash
mkdir testoutput
chmod +x testshowcase.sh
./testshowcase.sh
```


