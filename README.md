# WasmFXCert and Iris-WasmFX

This directory includes the supplementary artifact for the paper *Iris-WasmFX: Modular Reasoning
for Wasm Stack Switching*, a submission to **PLDI 2026**.

# Getting Started

## Browsing the Proofs

Once the artifact has been compiled (see step-by-step instructions), the proofs can be browsed using Emacs and Proof General. For example,

```bash
emacs theories/iris/examples/coroutines_implementation_code.v
```
opens the file containing the code and specification of the coroutines example from the paper. Other proofs can be browsed similarly. 


## Basic Testings

For some basic testing, the key coroutines example described in the paper resides in `theories/iris/examples/`, separated into three files as described in the proof of Theorem 5.1 from section 5.1 and Appendix E.1. The generator example described in section 5 is also in `theories/iris/examples/`. We invite the reviewers to run through the code and the fully-proved specifications of both example. 


# Step-by-Step Instructions

## Manual Installation and Compilation

The project can be installed using opam.

We recommend creating a new switch to start from a clean environment. We have compiled the project with version 4.14.2. The following code creates a switch with the necessary version:
```bash
opam switch create iris-wasmfx-artifact-switch ocaml.4.14.2
```

Depending on the opam configuration, it may be necessary to manually switch to the newly created switch:
```bash
opam switch iris-wasmfx-artifact-switch
eval $(opam env --switch iris-wasmfx-artifact-switch --set-switch)
```

The following code fetches all necessary dependencies from opam and compiles the development:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
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
emacs theories/iris/examples/iris_examples.v
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
opam install coq-iris.4.4.0
opam install mdx.2.5.0
```

Some packages are in the `coq-released` repository; in order to let opam know where to fetch these, before running `opam install` run:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
```

A shorthand to install all missing dependencies and compile the development is:
```bash
opam install .
```

### Warnings that are Safe to Ignore

When browsing the proofs in Emacs + Proof General, a warning on boolean coercion will pop up in the Coq response prompt when the theorem prover runs past the imports. This is because two of our dependencies, ssreflect and stdpp, each implements its own coercion of Bool into Prop, resulting in ambiguous coercion paths. However, this can be safely ignored since the two implementations are essentially the same.



## Claims Supported and Not Supported by the Artifact

This artifact is a fully-verified implementation in Coq of the program logic proposed in the paper supporting all claims of the paper. Some simplification has been made in the presentation of the paper for space constraints, and we have tried our best to highlight all such differences in the section `Differences with Paper` in the end.

We invite the reviewer to compare the key claims made in the paper against the code for a demonstration of completeness. We suggest starting from the coroutines example, which is the main running example in the paper, and the generator example, which is introduced in Section 5. Other examples, as well as the implementation of the program logic itself, can also be studied if interested. The detailed locations and an outline of them can be found under the `Structure` section below.

The remaining part of this readme aims to explain the structure of the artifact, and to provide directories and paths to locate the items that have appeared in the paper.


# Directories

For each figure and theorem in the paper, we provide the approximate paths, names and lines (where applicable) under `theories/`, to indicate the location of them in the code. We also provide a general pointer for each subsection in Section 3 and Section 4 for the related files in the codebase. For a detailed breakdown of the code structure, see the `Structure` section later.

| Location in Paper | Location in Code |
|--|--|
| Section 2 | `iris/examples/wat-code/` for the code, `iris/examples/coroutines_implementation_code.v` and `iris/examples/coroutines_client.v` for the specifications |
| Sections 3.2 and 3.3 | `datatypes.v` and `opsem.v` |
| Fig. 2 | `datatypes.v` |
| Fig. 3 | `iris/examples/wat-code/coroutine.wat` for the code, `iris/examples/coroutines_implementation_code.v` for the specifiaction |
| Section 3.4 | `typing.v` |
| Theorem 3.1 | `type_safety.v`, line 30 (and dependencies `type_preservation.v` and `type_progress.v` |
| Section 3.5 | `host.v` and `instantiation.v` for the definitions, `iris/instantiation/iris_instantiation.v` and `iris/host/iris_host.v` for the logic |
| Section 4.1 | `iris/language/iris_resources.v` for the resource definitions |
| Seciton 4.2 | `iris/language/protocols.v` and `iris/language/iris_ewp.v` |
| Fig. 5 | `iris/language/iris_ewp.v` |
| Sections 4.3 and 4.4 | `iris/rules/iris_rules_effects.v` |
| Fig. 6 | `iris/rules/iris_rules_effects.v` |
| Theorem 4.1 | `iris/rules/iris_rules_effects.v` |
| Theorem 4.2 | `iris/language/iris_adequacy.v` |
| Section 5 | `iris/examples/` |
| Theorem 5.1 | `iris/examples/coroutines_client.v`, line 1069 |
| Theorem 5.2 | `iris/examples/generator_client.v`, line 57 |


# Structure

In this section, we describe the structure of the implementation.

  
## WasmFXCert

Our work builds on the mechanisation of WebAssembly 1.0 by Watt et al. in *Two Mechanisations of WebAssembly, FM21*. As a result, our work inherits many files from Watt et al's mechanisised proofs, makes small changes to many files, and creates a few novel files. These files are located under `theories/`. We bring up the files most related to our work for completeness:

- `datatypes.v` contains all the basic stack switching data types definitions;

- `opsem.v` defines the operational semantics of stack switching;

- `typing.v` defines the type system for stack switching instructions, continuations, stores, and configurations.

- `instantiation.v` contains the definition of the module instantiation predicate in the official specification, as well as all the sub-predicates it depends on.


## Defining the Stack Switching Extensionin Iris

Under `theories/iris/language`, we instantiate the Iris Language framework with stack switching, and prepare the preambles for our program logic.


- `iris/iris.v`: instantiates Iris Language by defining the logical values, expressions, and proving the necessary properties for them etc.;

- `protocols.v`: defines the protocols used in the logic; this is borrowed directly from Hazel;

- `iris_resources.v`: defines all the resources used in IrisWasmFX

- `iris_ewp.v`, `iris_ewp_ctx.v`: sets up a custom extended weakest precondition to be used for our language, which differs from the standard constructs from Iris and Hazel, as described in the paper;

- `iris_adequacy.v`: establishes the adequacy theorem (4.2).

  

## Helper Properties for the Language

  
Under `theories/iris/helpers`, we establish a lot of auxiliary properties about either the stack switching semantics itself, or the plugging-in version of the semantics in Iris.

  

## Proof Rules for Stack Switching
  

Under `theories/iris/rules`, we proved a vast number of proof rules that can be used to reason about WebAssembly programs. Most of these rules are inherited directly from the earlier Iris-Wasm logic for plain WebAssembly. Our main contributions are in:

- `theories/iris/rules/iris_rules_effects.v`: contains proof rules for the stack switching specific instructions.

- `theories/iris/rules/iris_rules_exceptions.v`: contains proof rules for the exception handling suite.

The other files in the folder are mostly unchanged from Iris-Wasm, and are:

- `theories/iris/rules/iris_rules_pure.v`: contains proof rules for *pure* instructions, i.e. those whose reduction semantics are independent from the state (for example, the `wp_binop` rule in Line 260);

- `theories/iris/rules/iris_rules_control.v`: contains proof rules for control instructions;

- `theories/iris/rules/iris_rules_resources.v`: contains proof rules that directly access the state, such as memory instructions;

- `theories/iris/rules/iris_rules_call.v`: contains proof rules related to function calls;

- `theories/iris/rules/iris_rules_structural.v`: contains structural proof rules to deal with sequencing of instruction sequences, possibly within evaluation contexts;

- `theories/iris/rules/iris_rules_trap.v`: contains structural proof rules that allow reasoning when a part of the expression produce traps;

- `theories/iris/rules/iris_rules_bind.v`: contains several bind rules for binding into evaluation contexts;

- `theories/iris/rules/iris_rules.v`: imports everything above, allowing users to import all proof rules at the same time more easily.

  

## Host Language and Instantiation Lemma

Like plain WebAssembly code, stack switching code runs embedded in a host language. The earlier Iris-Wasm program logic for plain WebAssembly defined a custom host language that is able to instantiate WebAssembly modules and perform a few other operations. We have made minor modifications to these files to accomodate for stack switching.

- `theories/iris/instantiation/iris_instantiation.v` and `theories/iris/instantiation/instantiation_properties.v`: contains the module instantiation resource update lemma and other properties pertaining to module instantiation

- `theories/iris/host/iris_host.v`: defines a custom-made host language and establishes a set of proof rules for the host language required for reasoning about examples.


## Examples

Under `theories/iris/examples/effects`, we formulated the examples for our project, some of which were discussed in the paper. We bring up the key files below:

### Coroutines Example

- `coroutines_implementation_code.v`: contains the stack switching code for the coroutines example, and a proof of its specification

- `coroutines_module.v`: defines the coroutines module and proves its instantiation specification

- `coroutines_client.v`: defines a client module for the coroutines module, and proves its specification (theorem 5.1)

### Generator Example

- `generator.v`: contains the stack switching code for the generator example, and a proof of its specification

- `generator_module.v`: defines the generator module and proves its instantiation specification

- `generator_client.v`: defines a client module for the generator module, and proves its specification (theorem 5.2)

### Others

Other simpler examples can be found in the same folder, including one that uses the switch instruction: `iris_examples_effects_switch.v`. 


# Differences with Paper
  

## Definitions

The definitions within our work were designed in a way that would fit best in an interactive proof environment, to facilitate sustainable engineering in the long term. Therefore, some definitions, especially the constructors of inductive and records, are either named or designed in a verbose way.
  

There are two major categories of differences:
  

### Removing naming prefixes

In the code, we exercise a naming convention for most constructors of inductive definitions and record by adding prefixes to them, so that it is possible to deduce the source of these constructors by looking at the prefix. Oftentimes these prefixes are in acronyms of the source definition (for example, `BI_` for each constructor of basic instructions).

  

### Removing trivial constructors

  

The large records in WebAssembly often involve fields of the same type (for example, in the `instance` definition, the addresses of `functions`, `tables`, `memories`, and `globals` are all immediate (isomorphic to naturals). In the code, we sometimes add another layer of constructor for each of them when unintended uses are possible (for example, looking up in `tables` by using a `memory` export reference).

  

### Other differences in names


Some other name differences include:

- `suspend.addr` and `switch.addr` are (wrongly) called `suspend_desugared` and `switch_desugared` in the code; the translation process is (wrongly) referred to as desugaring in many constructor, function, and lemma names. This is a vestigial trace of a previous version where the term desugaring was appropriate. 

- We use the word 'instruction' a lot. As we illustrate in Fig. 2, these are actually separated into *basic instructions* and *administrative instructions*. Hence in our code, these are called `basic_instruction` and `administrative_instruction`, both of which are defined in `theories/datatypes.v`

- In Section 4.1, we introduce 'logical values'. In the code, these are called `val0` and are defined in `theories/iris/language/iris/iris.v` (line 17).

    




