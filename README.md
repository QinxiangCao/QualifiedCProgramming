# QCP: A Separation Logic Based C Verification Tool

QCP verifies annotated C programs by symbolic execution and emits proof
obligations for a proof backend. QCP supports both Rocq/Coq and Lean as formal
proof backends.

## Proof Backend

- **Rocq/Coq backend:** use Coq 8.20.1. The checker command names remain
  `coqc`, `coqtop`, and `coqdep`. The agent controller selects its build mode
  from the repository root: an `_build` directory uses Dune; otherwise it uses
  the lock-free exact Makefile workflow. Rocq 9.x is not supported.
- **Lean backend:** use the repository-pinned Lean toolchain under
  `Lean/lean-toolchain`. The setup scripts install or activate the matching
  Lean/Lake version.

You only need one backend to run QCP and verify annotated C programs. If you
are unsure which backend to use, start with Rocq/Coq, which currently has the
broadest support. Lean is a work in progress and only supports a subset of the
example set.

## Setup

Open the guide for your platform and install only the proof backend you plan to
use.

| Platform | Guide |
| --- | --- |
| Windows | [docs/windows-setup.md](docs/windows-setup.md) |
| Linux | [docs/linux-setup.md](docs/linux-setup.md) |
| macOS | [docs/macos-setup.md](docs/macos-setup.md) |

Windows users are suggested to use native PowerShell instead of WSL, especially
for beginners. WSL complicates Windows/Linux paths and editor tooling.

> Docker users can use the [devcontainer setup](docs/container-setup.md)
> for a quick reproducible Rocq environment. It is not needed for normal use;
> beginners should follow the platform guides above.

## QCP CLI

Use `symexec` to generate Rocq/Coq or Lean proof files from annotated C
programs. See [docs/qcp-cli.md](docs/qcp-cli.md).

## Repository Map

- `QCP_examples/`: annotated C input examples.
- `Rocq/`: Rocq/Coq libraries and generated verification artifacts.
- `Lean/`: Lean 4 migration and supporting Lake packages.
- `linux-binary/`, `win-binary/`, `mac-x86-64-binary/`, `mac-arm64-binary/`:
  prebuilt QCP executables.
- `run-example-linux.sh`, `run-example-windows.cmd`: Rocq-oriented example
  runners.
- `scripts/`: setup and build helpers.
- `tutorial/`: step-by-step QCP usage notes.
- `mcp/`: QCP and Rocq MCP integrations.
- `.agents/`, `AGENTS.md`, `AGENTS_WIN.md`: agent workflow contracts.

## Common Workflows

1. Use QIDE on an annotated C program to execute QCP incrementally and inspect
   assertions. See [docs/qide.md](docs/qide.md).
2. Run the QCP CLI to generate Rocq/Coq or Lean proof files.
3. Complete the remaining manual proofs in the generated backend files.
4. Check the proof files with the selected backend: Rocq/Coq or Lean.

## Evaluation

The evaluation examples live under `QCP_examples/`. Running the platform example
runner refreshes generated proof artifacts under `Rocq/examples/`, grouped by
the corresponding example subtree.

The VS Code extension component provides interactive verification support for
annotated C files. See [docs/qide.md](docs/qide.md).
