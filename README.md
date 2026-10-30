# QCP: A Separation Logic Based C Verification Tool

QCP verifies annotated C programs by symbolic execution and emits proof
obligations for a proof backend. QCP supports both Rocq/Coq and Lean as formal
proof backends.

## Getting Started

Choose one proof backend. If unsure, start with Rocq/Coq, which currently has
the broadest support. Lean is a work in progress and supports only a subset of
the examples.

- **Rocq/Coq backend:** use Coq 8.20.1. The checker command names remain
  `coqc`, `coqtop`, and `coqdep`. Rocq 9.x is not supported.
- **Lean backend:** use the repository-pinned Lean toolchain under
  `Lean/lean-toolchain`. The setup scripts install or activate the matching
  Lean/Lake version.

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

## Verification Workflow

1. Annotate a C program with specifications. Use [QIDE](docs/qide.md) for
   interactive symbolic execution and assertion inspection.
2. Generate Rocq/Coq or Lean verification files with
   [`symexec`](docs/qcp-cli.md). For Rocq files from `QCP_examples/`, see
   [Generating verification files](docs/generation.md).
3. Complete the remaining manual proofs in the generated files.
4. Check the proofs with the selected backend: Rocq/Coq or Lean.

## Repository Layout

- `QCP_examples/`: annotated C input examples; `verification/` holds the
  shared verification foundation, and `stdlib/`
  holds C standard-library specifications.
- `Rocq/`: Rocq/Coq libraries and generated verification artifacts.
- `Lean/`: Lean 4 migration and supporting Lake packages.
- `bin/`: prebuilt `symexec`, `StrategyCheck`, `lsp`, `mcp`, and `spec-check`
  executables for Windows, Linux, and macOS (arm64 and x86_64).
- `scripts/`: setup and build helpers.
- `tutorial/`: step-by-step QCP usage notes.
- `mcp/`: QCP and Rocq MCP integrations.
- `.agents/`, `AGENTS.md`: agent workflow contracts; Windows agent adaptation is
  documented in the [Windows workflow guide](.agents/skills/verification-orchestrator/docs/windows.md).
