# Linux Setup

This guide assumes native Linux. If your host is Windows, use
[windows-setup.md](windows-setup.md) instead; see the root
[README](../README.md) for the WSL recommendation.

## Prerequisites

Git is required to clone the repository.

On Ubuntu or Debian, install the common download/build tools with:

```bash
sudo apt update
sudo apt install -y git
```

For other distributions, install Git with the system package manager. See the
official [Git download guide](https://git-scm.com/download/linux). Verify it
before continuing:

```bash
git --version
```

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

## Proof Backend Setup

Choose one proof backend to install and use. If you are unsure, choose Rocq/Coq.

### Rocq/Coq

This repository requires **Coq 8.20.1**, which belongs to the Rocq project but
still uses the `coq` package and `coqc` command names. Rocq 9.x is not currently
supported. We recommend an isolated `opam` switch with OCaml 4.14.1:

```bash
sudo apt update
sudo apt install -y opam build-essential bubblewrap libgmp-dev pkg-config
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

The final command must report version 8.20.1. See the official
[Coq 8.20.1 release page](https://rocq-prover.org/releases/8.20.1) for the
matching source and opam instructions. In a new terminal, reactivate the
switch with `eval $(opam env --switch=qcp-rocq)`.

`dune --version` must report at least 3.16.1 for this repository.

Editor extensions are optional and are not required for command-line builds.

#### Build Rocq Files

Use Dune to build Rocq files with the opam setup above.

```bash
dune build -j4
```

Use a bounded job count. `-j4` means at most four concurrent jobs. Increase it
only when the machine has enough CPU and memory, and reduce or omit it after an
out-of-memory failure.

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

Use `linux-binary/symexec` directly. The following script is Rocq-only and
writes `.v` files under `Rocq/examples`:

- `run-example-linux.sh`

Lean-only users should run `run-example-lean-linux.sh` instead.

For command-line options, preprocessing, CRules imports, and Rocq/Lean
generation examples, see [qcp-cli.md](qcp-cli.md).

## MCP Setup

MCP is optional. Configure it according to [mcp-setup.md](mcp-setup.md).
