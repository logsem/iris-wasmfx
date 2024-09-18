# Step-by-Step Instructions

## Manual Installation and Compilation

The project can be installed using opam.

We recommend creating a new switch to start from a clean environment. The newest versions of ocaml are incompatible with our required version of Coq. We have compiled the project with version 4.13.1. The following code creates a switch with the necessary version:
```bash
opam switch create iris-wasm-artifact-switch ocaml.4.13.1
```

Depending on the opam configuration, it may be necessary to manually switch to the newly created switch:
```bash
opam switch iris-wasm-artifact-switch
eval $(opam env --switch iris-wasm-artifact-switch --set-switch)
```

The following code fetches all necessary dependencies from opam and compiles the development:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install .
```

If all necessary packages are present in the opam environment, the development can also be compiled by running
```bash
make
```

Compiling the development requires at least 8GB of RAM and may take over 30 minutes.

## Browsing the Proofs

Browsing proofs can be done conveniently in emacs. For example:

```bash
esy theories/iris/examples/iris_examples.v
```
This opens the file containing some direct examples of using the program logic in Emacs, assuming Emacs and Proof General are installed. Other proofs can be browsed similarly. Emacs can be installed via command line:
```bash
apt install emacs
```

The instruction to install Proof General can be found at https://proofgeneral.github.io.

Although not necessary, we also recommend installing the Company-Coq plugin for pretty printing and easier editing to the proofs. The instruction to install Company-Coq can be found at https://github.com/cpitclaudel/company-coq. Company-Coq is pre-installed in the VM image provided.

### Troubleshooting

If running `make` fails, the issue is likely a missing package in opam, or a package with the wrong version. Check what version of each package opam has registered by running `opam list`. A list of necessary packages and the requirements on their versions can be found in the `dune-project` file; in case of a discrepancy, the correct version can be manually installed.

Missing packages, or packages with the wrong version, can be installed manually using `opam install`. For instance, to get the correct version of `coq-iris` or `mdx`, run:
```bash
opam install coq-iris.dev.2023-06-30.0.7e865892
opam install mdx.2.4.1
```

Some packages are in the `coq-released` repository or in the iris development repository; in order to let opam know where to fetch these, before running `opam install` run:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

A shorthand to install all missing dependencies and compile the development is:
```bash
opam install .
```

### Warnings that are Safe to Ignore

When browsing the proofs in Emacs + Proof General, a warning on boolean coercion will pop up in the Coq response prompt when the theorem prover runs past the imports. This is because two of our dependencies, ssreflect and stdpp, each implements its own coercion of Bool into Prop, resulting in ambiguous coercion paths. However, this can be safely ignored since the two implementations are essentially the same.


