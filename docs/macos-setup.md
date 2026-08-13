# macOS Setup

This guide assumes native macOS.

## Prerequisites

Git is required to clone the repository.

Install Apple's Command Line Tools to obtain Git:

```bash
xcode-select --install
git --version
```

Alternatively, install current packages with Homebrew. See the official
[Git macOS guide](https://git-scm.com/download/mac) for other options.

Then, clone the repository:

```bash
git clone --recurse-submodules https://bitbucket.org/WxWyashen/qcp-binary-democases.git
cd qcp-binary-democases
```

To update an existing checkout, run:

```bash
git submodule sync --recursive
git submodule update --init --recursive
```

Choose the matching QCP binary directory for your Mac:

- Apple Silicon: `mac-arm64-binary/`
- Intel Mac: `mac-x86-64-binary/`

You can check with:

```bash
uname -m
```

## Proof Backend Setup

Choose one proof backend to install and use. If you are unsure, choose Rocq/Coq.

### Rocq/Coq

This repository requires **Coq 8.20.1**, which belongs to the Rocq project but
still uses the `coq` package and `coqc` command names. Rocq 9.x is not currently
supported.

The recommended command-line setup for this repository is the `opam` method
below. It works on both Apple Silicon and Intel Macs and creates an isolated
OCaml 4.14.1 switch. Install
[Homebrew](https://brew.sh/) first if `brew` is not already available:

```bash
brew install opam
opam init -y
opam update
opam switch create qcp-rocq ocaml-base-compiler.4.14.1
eval $(opam env --switch=qcp-rocq)
opam install coq.8.20.1
coqc --version
dune --version
```

Run `opam init` and `opam switch create` only the first time. If the
`qcp-rocq` switch already exists, skip those two commands and reactivate it
with `eval $(opam env --switch=qcp-rocq)`.

The final command must report version 8.20.1. In a new terminal, reactivate
the switch with `eval $(opam env --switch=qcp-rocq)`.

`dune --version` must report at least 3.16.1 for this repository.

An Apple Silicon GUI installer also exists in the official
[Coq Platform 2025.01.0 release](https://github.com/rocq-prover/platform/releases/tag/2025.01.0),
but the rest of this guide assumes the `opam` commands above so that `coqc` is
available in the terminal.

Ensure `coqc`, `coqtop`, and `dune` are on `PATH` before continuing.

#### Build Rocq Files

Use Dune to build Rocq files with the opam setup above.

```bash
dune build -j4
```

Use a bounded job count. `-j4` means at most four concurrent jobs. Adjust it
for available CPU and memory, and reduce or omit it after an out-of-memory
failure.

### Lean

Install Lean as described in [`../Lean/INSTALL.md`](../Lean/INSTALL.md), then
run the following from the QCP repository root. These commands do not use Rocq.

```bash
sh scripts/build-lean.sh build
sh scripts/build-lean.sh clean
```

You can also use the aggregate Makefile directly:

```bash
cd Lean
make build
make clean
```

## VS Code Setup

- Configure QIDE according to [qide.md](qide.md).
- Configure VsRocq/VsCoq according to [vsrocq-setup.md](vsrocq-setup.md).

## QCP Command-Line Tool

Use the matching `symexec` binary from your macOS directory.

Use `mac-arm64-binary/symexec` on Apple Silicon and
`mac-x86-64-binary/symexec` on Intel Mac.

For command-line options, preprocessing, CRules imports, and Rocq/Lean
generation examples, see [qcp-cli.md](qcp-cli.md).

## MCP Setup

MCP is optional. Configure it according to [mcp-setup.md](mcp-setup.md).
