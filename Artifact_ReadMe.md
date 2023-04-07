In our artifact, we describe two ways of interacting. One is building from the source code (`FPOP.zip`), the other is directly using docker image (`FPOPtest1.tar`).

1. Our plugin needs to work in OCaml base compiler 4.13.1 and
Coq 8.15.0, so when building the source, this is required.

2. The docker container is created in x86-64 ubuntu machine so it might be slower on a different CPU/OS. 

***

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




***
# Docker Artifact for FPOP

We also directedly distribute docker for artifact evaluation. Artifact is already built on an x86-64 Ubuntu machine and can be used out of box. 

Note: The current implementation focus on **the implementation simplicity and functional correctness**, so it is quite **inefficient**. We are undergoing optimization and refactorization for more use-cases.

Note 2: The docker is created from a  
* 8cpu, 11th Gen Intel(R) Core(TM) i7-1165G7 @ 2.80GHz
* 16GM RAM

machine. SO all the following info (including coq running time) is mainly tested on that. 


* All the tests files are located in `showcase_test`, where all the examples and showcases promised in the paper locates

* We will mark __†EFFECTFUL CHANGE†__ to those instructions that may change the evaluators' PC

## Connect to docker, Verify the Proof (10 mins to read)

**Section Target:** We will show our plugin is capable of type-checking the new feature, *Family Polymorphism*, proposed in the paper. Thus in this part, we evaluate our artifact by simply running successfully all the proof scripts that are using our feature. 

In this section, we prepare and connect to the docker. We will require docker to be installed, so it is a effectful change for those didn't install docker.

### Install Docker
__†EFFECTFUL CHANGE†__

We refer the reader to [the official documents](https://docs.docker.com/engine/install/). Side Note: We prepare the artifact by [installing docker enginer on ubuntu](https://docs.docker.com/engine/install/ubuntu/).

### Prepare Image, Attach to Docker's terminal, Setup
__†EFFECTFUL CHANGE†__

1. We first import docker container file `FPOPtest1.tar`
```bash
> sudo docker import FPOPtest1.tar fpopeval
```
We should be able to see `fpopeval` in `sudo docker images`.

For the following steps, we will require using `sudo` as well. If the evaluator doesn't want to, they can refer to [the official document of adding current user to docker group](https://docs.docker.com/engine/install/linux-postinstall/#manage-docker-as-a-non-root-user).


2. Now we connect to docker and load this new image
```bash
> sudo docker run -i -t fpopeval /bin/bash
```
3. Our artifact locates in `/home/FPOP`, we also need to prepare `opam`
```bash
> cd /home/FPOP
> eval $(opam env)
```
Every opam command is done in root mode so the opam will constantly give warning.

4. (optional) build, as we already build everything in the container, this should succeed. But we may want to check opam sets up the environment correctly

```bash
> dune build
```
  * If the evaluator wants to build our Coq plugin, in the current docker file, in folder `FPOP`, `dune build` is enough to build the Coq Plugin.
    * It will rebuild the files in the directory `src` and `theory` 
  * build time should < 1 min 


### Verify the proof, using coqc 

`coqc` is the compiler version of Coq, without the ability of interactive theorem proving. It can be used to check if a coq `.v` file completes the proof.



**Note: The current implementation will generate a lot of debug dump during the following `coqc` commands and we haven't implemented how to turn it off. So we suggest the evaluator to redirect all the command output into a file to make sure that the terminal display is clean**


All the following command should be emitted in the directory `/home/FPOP`

* To run a specific file, we use 
```bash
> coqc showcase_test/[file.v] -R _build/default/theories Fampoly -I _build/default/src
```
* To redirect the output dump to `output`, we further use
```bash
> coqc showcase_test/[file.v] -R _build/default/theories Fampoly -I _build/default/src &> output.txt
```
Because there will be a lot of dump in the text, we can use `less +G output.txt` to view the file from the end.

#### **Each file took time**

Now for each file 
```bash
> coqc showcase_test/Analysis_showcase.v -R _build/default/theories Fampoly -I _build/default/src
```
(Coq check time ~ 3min30s)
```bash
> coqc showcase_test/Analysis_showcase2.v -R _build/default/theories Fampoly -I _build/default/src
```
(Coq check time ~ 3min30s)
```bash
> coqc showcase_test/Grammar_test6.v -R _build/default/theories Fampoly -I _build/default/src
```

(Coq check time ~ 6s)
```bash
> coqc showcase_test/mixin2.v -R _build/default/theories Fampoly -I _build/default/src
```
(Coq check time ~ 10min30s)
```bash
> coqc showcase_test/STLC_families.v -R _build/default/theories Fampoly -I _build/default/src
```
(Coq check time ~ 9min)
```bash
> coqc showcase_test/test34.v -R _build/default/theories Fampoly -I _build/default/src
```
(Coq check time < 1s)




## Interactively look at the proof, using VSCode Docker Remote + VSCoq (10 mins to read) 

**Section Target:** Another big part of our artifact is its integratbility with the existing Coq programming experience. To illustrate this advantage, we provide the evaluator a better programming interface to interact with our plugin. The evaluator can also take a look at the proof scripts that uses our features. 

In this section, we use VSCode + VSCoq to open each of the files in `showcase_test`. Technically speaking, this guide here is about opening the file with VSCode Docker Remote + VSCoq. So that evaluator can have a better view on what each proof is about.

We will utilize the VSCode docker remote, so it is a effectful change that will happens to the outside of the docker.

### Install VSCode 
__†EFFECTFUL CHANGE†__

We suggest referring to [the official document.](https://code.visualstudio.com/download)

### Attach VSCode to the docker, use VSCode Remote + VSCoq
__†EFFECTFUL CHANGE†__

1. Make sure the current user is able to execute `docker` without `sudo`,
   1. Check https://stackoverflow.com/questions/57840395/permission-issue-using-remote-development-extension-to-attach-to-a-docker-image for details
   2. The reason here is that, [on Ubuntu 21, VSCode cannot be runned as root](https://github.com/microsoft/vscode/issues/146445)
      1. I am not sure if this is a Ubuntu-only problem
2. Install VSCode *Remote Development* pack, make sure *Dev Containers* extension is enabled
3. Open the *Remote Explorer* at the side bar, at the left-top make sure REMOTE EXPLORER is aiming at `Containers` (instead of `SSH` or other things)
4. then there should be some containers in *Containers*, if not, use docker to run/create a container from our image
5. Move mouse to that container, you should be able to see *Attach to container* button, once clicked, a new window of VSCode should open
6. Install *VSCoq* extension in the new window VSCode
   1. this should make *VSCode Server* that locates in the container to install VSCoq properly
7. open the folder `/home/FPOP` in the new window VSCode
   1. after opening the folder, make sure `VSCoq` is enabled


### Open Proof Files, Interactively go through the proof

Now you should be able to open arbitrary files in `showcase_test` directory, and `VSCoq` should render the syntax highlighting properly.

Press (ALT + ↓) should be next proof step. Look at *Command Pallette* (CTRL+SHIFT+P), you shoud be able to see all the Coq interactive command here, by typing `Coq` the palette will try to autocomplete the command you want.

Now feel free to (ALT + ↓) and (ALT + ↑). Note that, some commands are very slow, especially when you hit `FEnd ...` (when closing a family).

# Paper Example to Coq Proof Correspondence
* (Line 245) Figure 2 is the simple version of `showcase_test/STLC_families.v`: around Line 76, `Family STLC`
* (Line 327) Section 3.3 Feature *Overriding* is mainly used in `showcase_test/Analysis_showcase.v` and `showcase_test/Analysis_showcase2.v`
* (Line 344) Figure 3 (Also Sec 3.5) `STLCIsorec` locates in  `showcase_test/mixin2.v`: around Line 968 `Family STLC_isorec`
* (Line 344) Figure 3 (Also Sec 3.5) `STLCProd` locates in  `showcase_test/mixin2.v`: around Line 443 `Family STLC_prod` 
* (Line 354) Figure 3 (Also Sec 3.5) `STLCProdIsorec` locates in `showcase_test/mixin2.v`: around Line 1334 `Family STLC_prod_isorec`
* (Line 362) Figure 3 (Also Sec 3.5) `STLCFixIsorec`  locates in `showcase_test/mixin2.v`: around Line 1326 `Family STLC_fix_isorec`
* (Line 362) Figure 3 (Also Sec 3.5) `STLCFixProdIsorec`  locates in `showcase_test/mixin2.v`: around Line 1354 `Family STLC_fix_prod_isorec`
* (Line 401) Section 3.6 `finjection` and `fdiscriminate` are used in `showcase_test/test34.v` around Line 30 and Line 35
* (Line 406) Section 3.6 *partial recursor* is currently generated using a `FScheme` command, one example is in `showcase_test/test34.v` around Line 24.
* The plugin implementation is basically located in `src/` and mirroring Section 4
* Section 6, Type Safety of STLCs locates in `showcase_test/STLC_families.v` and `showcase_test/mixin2.v`. 
  * All the mixin between `STLC_Prod`, `STLC_Fix`, `STLC_Bool` and `STLC_sum` locates in `showcase_test/STLC_families.v` from Line 1308~1344
    * The evaluator can check the comments and uncomment the vernacular command as they want
  * Mixin on `STLC_Prod`, `STLC_Fix` and `STLC_isorec` locates in `showcase_test/mixin2.v` mentioned above
* Section 6, Abstract interpreters for imperative languages, locates in `showcase_test/Analysis_showcase.v` and `showcase_test/Analysis_showcase2.v`
  * We separate them into two files. Technically they can be in one files but our plugin is currently too inefficient and put them all in one files will lead to memory/stack overflow during translation
  * (Line 896) "retains the computation ability of the host proof assistant" is shown in both examples -- `showcase_test/Analysis_showcase.v` and `showcase_test/Analysis_showcase2.v` at the file end, we show program extraction.
    * The extract ocaml file locates in `testoutput/`
    * The evaluator can choose to load them in OCaml (specifically utop to run)
* (Line 902) "modeling extensible context-free grammars" locates in `showcase_test/Grammar_test6.v`, the decision procedure are `is_prog_dec` and `is_exp_dec` in that file. The decision procedure is a naive one (thus easy to prove)
  * We also support extraction on this CFG (i.e. `is_prog_dec` and `is_exp_dec` can be extracted to OCaml)
  
# Appendix : Load Extracted OCaml file

We take `showcase_test/Analysis_showcase.v` as an example. Once the above mentioned `coqc` command is done, we can enter `testoutput/`
```bash
> cd testoutput/
```
In our docker, utop is not yet installed, 
```bash
> opam install utop
```
We should be able to see some ocaml files now. Let's load them.
```ocaml
> utop
> #use "test2.ml" ;;
```
After loaded it, we can see in `LangCPTesing` there are several test-cases can be run, for example we can run

```bash
> LangCPTesing.testcase1 ();;
```
This should run the first testcase and result the correct answer `natlit 1`. Other examples like `Analysis_showcase2.v`, `Grammar_test6.v` can be treated similarly.


# Appendix : Directory Structure
1. `showcase_test/` includes all the showcase included in the paper 
2. `src/` and `theories/` includes all the source code of our plugin. `LibTactics.v` and `Maps.v` are directly from Software Foundation
## about `src` directory
1. `src/familytype.ml` contains the main functionality of our plugin, including the internal data structure (representing the family) and the translation from this internal data structure to Coq's command.
2.  `src/fampoly.mlg` is the `mlg` file extending the Vernacular syntax for our plugin
3.  `src/famprogram.ml` mainly interacts with the users. It contains the function that `fampoly.mlg` will invoke
4. `src/fenv.ml` handles the environment/definitions of the families in our internal structure
5. `src/finduction.ml` implements the `FRecursion` facility
6.  `src/finh.ml` implements the inheritance facility
7.  `src/ftheorem.ml` makes it possible to use Coq Proof Mode and Coq tactic to work with our plugin
8.  `src/utils` and `src/CCCache.ml` are helpers. `CCCache.ml` is directly copied from `OCaml-containers` (Thanks Simon Cruanes!)

