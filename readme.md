# Bisimulation and coinductive types in the Rocq proof assistant

## Installation instructions

### Using jscoq

If you do not have a local installation of Rocq, you may access the development directly in your browser at the following address:

https://x80.org/epit-2025/cats.html

Many thanks to Emilio Jesús Gallego Arias or setting it up for us!

### Using Opam

#### Coq/Rocq

The development should compile out of the box with Coq `>== 8.17` and `<= 8.20`.
In particular, it will fail with `9.0`.

If you do not have a suitable version yet, we hence suggest:

> `opam pin add coq 8.20.1`

#### External dependencies

If it is the first time you install rocq libraries with `opam`, you will have to run the following command:

> `opam repo add rocq-released https://rocq-prover.org/opam/released`

We only depend on the `coq-coinduction` library, that can be obtained with 

> `opam install coq-coinduction`

#### vscoq

If you want to use vscode as your editor, you will need to additionally install the vscoq server:

> `opam install vscoq-language-server`

You then need to set the `VScoq: Path` variable to point to your `coqtop`, i.e., something like `/Users/yourusername/.opam/yourswitchname/bin/vscoqtop`

#### rocqide

Alternative ide.

> `opam install rocqide`

## Compiling

### Using dune

If you are using dune, simply run:

> `dune build`

### Without dune

If you do not want to use dune, replace the `_CoqProject` file by its alternative `nodune_CoqProject`. You can then run the following commands:

> `coq_makefile -f _CoqProject -o CoqMakefile`
> ``make -f CoqMakefile`
