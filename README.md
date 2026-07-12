# QCP: A Practical Separation Logic-based C Program Verification Tool

## File Structure
- `linux-binary/`, `win-binary/`, `mac-x86-64-binary/`, `mac-arm64-binary/`: Precompiled QCP binaries, including `symexec`, `StrategyCheck`, `lsp`, and `mcp`.
- `QCP_examples/`: Annotated C programs used as QCP inputs. Current subtrees are `Applications_human/`, `QCP_demos_human/`, `QCP_demos_LLM/`, `QCP_demos_tutorial/`, and `LLM_bench/`.
- `SeparationLogic/`: Rocq libraries and generated verification artifacts used to check QCP-generated VCs. Its `examples/` subtree mirrors the main `QCP_examples/` layout.
- `mcp/`: MCP server integrations. `mcp/qcp-mcp/` provides the QCP MCP server, and `mcp/rocq-mcp/` is a submodule for Rocq interaction.
- `.agents/`: Agent-facing verification workflow assets. It contains local skills for orchestration, annotation, VC checking, VC proving, and final consistency checks.
- `AGENTS.md`, `AGENTS_WIN.md`: Repository-level contracts for agent-driven verification workflows. Linux/macOS use `AGENTS.md`; Windows uses `AGENTS_WIN.md`.
- `README_LINUX.md`, `README_WINDOWS.md`, `README_MACOS.md`: Platform-specific setup guides.
- `.codex/`, `.vscode/`, `.devcontainer/`: Local agent/editor/container configuration.
- `scripts/`: Utility scripts for repository-level analysis.
- `tutorial/`: Step-by-step QCP usage guide.
- `run-example-linux.sh`, `run-example-windows.cmd`: Scripts that run QCP examples and refresh generated Rocq files.
- `categories.json`, `categories.md`: Case categorization metadata.
- `qide.vsix`: QCP VS Code extension.
- `vscoq-2.2.3.vsix`: Windows-tested VsCoq extension package for Coq 8.20 proof interaction.


## Environment Setup

We provide two environment setup options:

1. Non-Docker local environment setup (build and run directly on your host machine).
2. Docker-based environment setup.

You can choose either option according to your needs.

### Local Environment Setup

#### Prerequisites
- Rocq 8.20.1 (Coq 8.20.1), recommended with OCaml 4.14.1

Optional (only if you use MCP locally):
- `uv` (for `qcp-mcp` / `rocq-mcp` Python environment)
- `opam` + `coq-lsp` (for `rocq-mcp` interactive tools)

#### Platform-Specific Local Setup

Choose the guide for your platform:

- [Linux local setup](README_LINUX.md#local-environment-setup)
- [Windows local setup](README_WINDOWS.md#local-environment-setup)
- [macOS local setup](README_MACOS.md#local-environment-setup)

#### Rocq Files Build

Then you can compile Rocq files:

```bash
cd SeparationLogic/unifysl
make depend && make
cd ..
make depend && make
```

If you only want part of the generated files under `SeparationLogic/examples`, the build targets are split by the current example groups:

```bash
cd SeparationLogic

# Core libraries only
make depend-core && make core

# All generated examples
make depend-examples && make examples

# Only one examples subtree
make depend-examples-applications && make examples-applications
make depend-examples-qcp-democases && make examples-qcp-democases
make depend-examples-qcp-demo-tutorial && make examples-qcp-demo-tutorial
make depend-examples-llm-friendly-cases && make examples-llm-friendly-cases
make depend-examples-llm-bench && make examples-llm-bench

# Clean outputs without removing everything
make clean-core
make clean-examples
make clean-examples-applications
make clean-examples-qcp-democases
make clean-examples-qcp-demo-tutorial
make clean-examples-llm-friendly-cases
make clean-examples-llm-bench
make clean-deps
```

This is useful because `SeparationLogic/examples` is organized into `Applications_human`, `QCP_demos_human`, `QCP_demos_LLM`, `QCP_demos_tutorial`, and `LLM_bench`, and you no longer need to regenerate dependencies for all example folders every time.
The clean targets follow the same split, so you can remove only core outputs, all example outputs, one example subtree, or just the generated dependency files.

### Docker Environment Setup

#### Prerequisites

- Docker installed ([Get Docker](https://docs.docker.com/get-docker/))
- Visual Studio Code ([Download](https://code.visualstudio.com/))
- VS Code Remote - Containers extension ([Install](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers))

#### Build the Docker Image

Open a terminal in the project root and run:

```sh
docker build --build-arg MAKE_JOBS=5 -t qcp .
```

This will build the Docker image using the provided `Dockerfile`.

#### Run VS Code Devcontainer

1. Check the `.devcontainer/devcontainer.json` file exists in the project root.
2. Open the project root folder in VS Code.
3. When prompted, click "Reopen in Container" or use the command palette:
   - `Ctrl+Shift+P` → "Dev Containers: Reopen in Container"
4. VS Code will build the container and set up the environment automatically.

## QIDE Extension

### Setup

The QIDE extension for VS Code should be automatically installed and configured when using the devcontainer setup. If not, follow these steps:

- Install the QIDE extension from the VS Code UI.
  (Note that we did not publish the extension to the marketplace, so do not search for it in the extensions shop.)
  - Open the command palette (`Ctrl+Shift+P`)
  - Select "Extensions: Install from VSIX..."
  - Choose the VSIX file `qide.vsix` from the project root.
- QIDE extension settings: open `File > Preferences > Settings`, search for `qide`, and set:
  - `qide.lspBinPath` to the platform-specific `lsp` binary path
  - `qide.lspArg` is the execution options for QCP. You can leave it empty refer to `Options to run QCP`.

Platform-specific QIDE notes:

- [Linux QIDE setup](README_LINUX.md#qide-extension)
- [Windows QIDE setup](README_WINDOWS.md#qide-extension)
- [macOS QIDE setup](README_MACOS.md#qide-extension)

### Usage

- Open an annotated C program.
- Move the cursor to any place you like and press `Alt+Rightarrow`.
  You can change the keyboard shortcuts settings if needed.
  You can also run the command `qide.interpretToPoint` directly from the command palette (`Ctrl+Shift+P`).

### QCP Command-Line Tool

The `run-example-linux.sh` and `run-example-windows.cmd` scripts in the root directory give examples of how to run QCP command-line tool. You can directly execute them if you have the required environment set up. The Windows script runs natively from both Command Prompt and PowerShell and does not require Bash.

Platform-specific command-line notes:

- [Linux command-line usage](README_LINUX.md#qcp-command-line-tool)
- [Windows command-line usage](README_WINDOWS.md#qcp-command-line-tool)
- [macOS command-line usage](README_MACOS.md#qcp-command-line-tool)

For VS Code Rocq/Coq proof interaction on Windows with Coq 8.20, use the repository-local [Windows proof extension setup](README_WINDOWS.md#vs-code-coq-proof-extension).

Below is a summary of the main command-line options of QCP. We also recommend following the tutorials in the `tutorial/` folder for a comprehensive guide.

**Usage:**
```text
linux-binary/symexec [options]
```

**Required options:**
- `--input-file=<file>`: Specify the input C source code.
- `--goal-file=<file>`: Output file for generated verification conditions (VCs).
- `--proof-auto-file=<file>`: Output file for automatically solved VCs.
- `--proof-manual-file=<file>`: Output file for VCs requiring manual proofs.

**Optional flags:**
- `--gen-and-backup`: If output files exist, back them up before overwriting; otherwise, only "proof-manual" is backed up.
- `--no-exec-info`: Suppress intermediate information during symbolic execution.
- `--coq-logic-path=<path>`: Specify the Coq logic path for the goal file.
- `-slp <dir> <path>`: Add a directory to the strategy search paths.
- `-I<dir>`: Add a directory to the include search paths.
- `--compile-commands <file>`: Read include paths from a `compile_commands.json` compilation database.
- `--float-finite-vc`: Generate finite-value safety VCs for floating-point operations.
- `--no-float-finite-vc`: Do not generate finite-value safety VCs for floating-point operations.
- `--strategy-application-limit <count>`: Stop a solver run after the given number of successful strategy applications. The default is `4096`; valid values range from `1` to `100000000`.

**Preprocessing:**
QCP has a built-in C preprocessor, so source files do not need to be passed through `cpp` first. It supports object-like and function-like macros in both ordinary C expressions and annotations, nested conditional directives (`#if`, `#ifdef`, `#ifndef`, `#elif`, `#else`, and `#endif`), quoted and angle-bracket includes, include guards, and `#pragma once`.

Use `-I<dir>` to add include search paths, or `--compile-commands <file>` to load them from a compilation database. Macro expansion preserves original source locations for diagnostics. Pass `--debug-preprocessor` when you need to inspect macro expansions.

**Coq Integration:**
The generated `.v` files must be used with SeparationLogic. For details, see `SeparationLogic/README.md`.

## MCP Setup

The `mcp/rocq-mcp` directory is a git submodule. Before configuring MCP, make sure submodule content is initialized and up to date.

From the project root:

```bash
# Initialize and update submodules
git submodule sync --recursive
git submodule update --init --recursive
```

After updating submodules, verify `mcp/rocq-mcp/README.md` exists.

Platform-specific MCP setup:

- [Linux MCP setup](README_LINUX.md#mcp-setup)
- [Windows MCP setup](README_WINDOWS.md#mcp-setup)
- [macOS MCP setup](README_MACOS.md#mcp-setup)

For more details, refer to:
- `mcp/qcp-mcp/README.md`
- `mcp/rocq-mcp/README.md`

## Agent Verification Workflow

The repository includes agent-specific instructions for running a complete verification case, not just isolated edits. Choose the platform-specific entry point first, then use the detailed phase contracts under `.agents/skills/`.

Platform-specific agent entry points:

- Linux: `AGENTS.md`
- macOS: `AGENTS.md`
- Windows: `AGENTS_WIN.md`

All three platforms share the same skill set under `.agents/skills/`. Windows-specific execution differences are documented in `AGENTS_WIN.md`; there is no separate Windows-only skill tree.

The supported verification modes are:

- `direct proof`: annotate a C program, run symbolic execution, prove generated Rocq VCs, and perform final checks.
- `refinement proof`: relate a C program to an abstract monadic program, prove the refinement obligations, and finish the same Rocq/final-check workflow.

The phase state machine is:

```text
intake -> annotation -> goal-frozen -> vc-checking -> vc-proving -> final-check -> done
```

Downstream phases may return to `annotation` or `vc-proving` when they expose stale inputs, annotation bugs, or proof obligations that require earlier fixes.

### Agent Roles

- Main agent: owns phase transitions, official file writes, symbolic execution, Rocq compilation, final checks, and case status records.
- `annotation-subagent`: works only in annotation scratch files, uses `annotation-filling`, and runs `annotation-checking` before anything is integrated into official files.
- `vc-checking-subagent`: uses `vc-checking` to classify manual VCs and produce proof grouping hints.
- `vc-proving-subagent`: uses `vc-proving` to prove manual VCs in proving scratch files, normally through the scripted concurrent worker pipeline.

### Agent Skills

- `.agents/skills/verification-orchestrator/`: phase ownership, state machine, scratch lifecycle, formal file boundaries, artifact templates, and stale-input rules.
- `.agents/skills/annotation-filling/`: spec-first and predicate-first C annotation work using isolated annotation C scratch plus `annotation_scratch_lib`.
- `.agents/skills/annotation-checking/`: quality gate for mathematical specs, function contracts, assertions, and loop invariants before official integration.
- `.agents/skills/vc-checking/`: semantic triage of generated VCs and proof group planning.
- `.agents/skills/vc-proving/`: scripted proof splitting, worker preparation, concurrent proving, validation, helper migration, and manual proof verification.
- `.agents/skills/final-check/`: final structure audit, symexec freshness check, Rocq compilation, `Admitted`/extra `Axiom` review, and cleanup checks.
- `.agents/skills/annotation-and-symbolic-execution/`: legacy annotation workflow kept for compatibility; new cases should use `annotation-filling` plus `annotation-checking`.

## Evaluation

Our evaluation consists of two parts: the Tool component and the VSCode Extension component.
- The Tool component allows you to check files in the ``QCP_examples`` tree by running ``sh ./run-example-linux.sh``, and it generates the corresponding Coq files in the ``SeparationLogic/examples/`` directory, grouped under ``Applications_human/``, ``QCP_demos_human/``, ``QCP_demos_LLM/``, ``QCP_demos_tutorial/``, and ``LLM_bench/``. Tutorial examples include the step-by-step swap cases and branch-control examples.
- The Rocq build in ``SeparationLogic/`` mirrors this layout with folder-specific targets: ``examples-applications``, ``examples-qcp-democases``, ``examples-qcp-demo-tutorial``, ``examples-llm-friendly-cases``, and ``examples-llm-bench``, together with matching ``depend-examples-*`` targets.
- The VSCode Extension component is designed to support real-time verification interaction. You can open any annotated C file to view the current assertion state, which facilitates the continued writing of annotations for proofs.
