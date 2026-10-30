# Generating Verification Files

Generate Rocq verification files from `QCP_examples/` using Dune or the Python
runner. Run commands from the repository root.

## Dune

Generate files for all C programs and non-builtin strategies:

```sh
dune build -j4 @gen-vcs
```

For individual inputs, use paths relative to `QCP_examples/`:

```sh
dune build @gen-vcs/QCP_demos_LLM/simple_arith/add.c
dune build @gen-vcs/verification/array2.strategies
```

To generate every C program and non-builtin strategy below a directory, build
the corresponding directory below `gen-vcs/` (the trailing slash is optional):

```sh
dune build -j16 gen-vcs/LLM_bench/
dune build -j16 gen-vcs/LLM_bench/Algorithms/
```

These directory targets are opt-in; a plain `dune build` does not run VC
generation.

Dune shows differences without updating source files. Accept them with
`dune promote`, or generate and accept changes together:

```sh
dune build -j4 @gen-vcs --auto-promote
```

Existing manual proofs in the source tree are preserved. Missing manual proofs
will be initialized from the generated template manual proof upon promotion.

If generation stops because configuration or builtin exports changed, promote
those changes and rerun the command. This also applies with `--auto-promote`.

## Python runner

```sh
# List all tasks without generating files
python3 scripts/generate.py --list
# Generate all tasks with 4 parallel jobs (default is 1)
python3 scripts/generate.py --jobs 4
# Or select one or more task types to generate:
python3 scripts/generate.py program --jobs 4
python3 scripts/generate.py strategy --jobs 4
```

Existing manual proofs are preserved; no promotion step is needed.

## Maintainer workflows

Whenever the source layout changes, regenerate the Dune configuration:

```sh
dune build @gen-dune-config --auto-promote
```

When updating the QCP binaries in `bin/`, regenerate the builtin strategies and
verification files:

```sh
dune build @gen-builtin --auto-promote
# Or with the Python runner:
# python3 scripts/generate.py builtin

# Then check the proofs:
dune build -j4 Rocq/Verification/BuiltIn/
```
