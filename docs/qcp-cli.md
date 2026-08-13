# QCP Command-Line Tool

QCP's command-line executable is `symexec`. It reads annotated C files and can
generate Rocq/Coq proof artifacts, Lean proof artifacts, or both.

Use the binary for your platform:

| Platform | Binary |
| --- | --- |
| Linux | `linux-binary/symexec` |
| Windows | `win-binary/symexec.exe` |
| macOS Apple Silicon | `mac-arm64-binary/symexec` |
| macOS Intel | `mac-x86-64-binary/symexec` |

The root example runners are convenience wrappers:

- `run-example-linux.sh` and `run-example-windows.cmd` are Rocq-only and
  refresh `.v` files under `Rocq/examples`.
- `run-example-lean-linux.sh` and
  `run-example-lean-windows.cmd` generate Lean artifacts for the migrated
  Lean example set.

## Usage

```text
linux-binary/symexec [options]
```

On Windows, replace `linux-binary/symexec` with `.\win-binary\symexec.exe`.
On macOS, use the matching `mac-*-binary/symexec` executable.

We also recommend following the tutorials in the
[`tutorial/`](../tutorial/) directory for a comprehensive guide.

## Common Options

- `--input-file=<file>`: specify the input C source code.
- `--coq-output-dir <dir>`: derive generated Rocq/Coq file paths from an
  output folder.
- `--lean-output-dir <dir>`: enable Lean generation and derive generated Lean
  file paths from an output folder.
- `--goal-file=<file>`: output file for generated verification conditions
  (VCs).
- `--proof-auto-file=<file>`: output file for automatically solved VCs.
- `--proof-manual-file=<file>`: output file for VCs requiring manual proofs.

## Optional Flags

- `--gen-and-backup`: if output files exist, back them up before overwriting;
  otherwise, only `proof-manual` is backed up.
- `--no-coq-gen`: disable all Rocq/Coq file generation.
- `--no-lean-gen`: disable all Lean file generation.
- `--program-path <file>`: write the generated Rocq/Coq program to a file.
- `--no-exec-info`: suppress intermediate information during symbolic
  execution.
- `--coq-logic-path=<path>`: specify the Coq logic path for the goal file.
- `--lean-logic-path <path>`: specify the Lean import prefix for generated
  files.
- `-slp <dir> <path>`: add a directory to the strategy search paths.
- `-I<dir>`: add a directory to the include search paths.
- `--compile-commands <file>`: read include paths from a
  `compile_commands.json` compilation database.
- `--CRules <module>`: import the given C rules module in generated Rocq/Coq
  files. The default is selected from `--arch` and `--endian`.
- `--arch <32|64>`: select the target C architecture width. The default is
  `32`; use `--arch=64` for 64-bit pointer size and 64-bit default CRules.
- `--endian <big|little>`: select the target byte order. The default is `big`;
  little-endian mode uses the `Snaive_*` default CRules modules unless
  `--CRules` is specified explicitly.
- `--no-CRules`: do not automatically import the default C rules module.
- `--float-finite-vc`: generate finite-value safety VCs for floating-point
  operations.
- `--no-float-finite-vc`: do not generate finite-value safety VCs for
  floating-point operations.
- `--strategy-application-limit <count>`: stop a solver run after the given
  number of successful strategy applications. The default is `4096`; valid
  values range from `1` to `100000000`.

## Preprocessing

QCP has a built-in C preprocessor, so source files do not need to be passed
through `cpp` first. It supports object-like and function-like macros in both
ordinary C expressions and annotations, nested conditional directives (`#if`,
`#ifdef`, `#ifndef`, `#elif`, `#else`, and `#endif`), quoted and angle-bracket
includes, include guards, and `#pragma once`.

Use `-I<dir>` to add include search paths, or `--compile-commands <file>` to
load them from a compilation database. Macro expansion preserves original
source locations for diagnostics. Pass `--debug-preprocessor` when you need to
inspect macro expansions.

## Rocq/Coq Generation

The generated `.v` files must be used with Rocq/Coq 8.20.1. For build details,
see [Rocq/README.md](../Rocq/README.md).

For VS Code Rocq/Coq proof interaction, see
[vsrocq-setup.md](vsrocq-setup.md).

By default, `--arch=32 --endian=big` adds the following import to generated
Rocq/Coq files:

```coq
Import naive_C_Rules.
```

Unless `--CRules` is given explicitly, the default import is selected from
`--arch` and `--endian`:

| Options | Default import |
| --- | --- |
| `--arch=32 --endian=big` | `Import naive_C_Rules.` |
| `--arch=64 --endian=big` | `Import naive_C_Rules64.` |
| `--arch=32 --endian=little` | `Import Snaive_C_Rules.` |
| `--arch=64 --endian=little` | `Import Snaive_C_Rules64.` |

The architecture option affects `sizeof(T *)`: the default 32-bit mode gives
`sizeof(T *) = 4`, and 64-bit mode gives `sizeof(T *) = 8`. It also controls
address/size-related frontend constants such as `SIZE_MAX`, `PTR_MAX`, and
`ADDR_MAX`.

Use `--CRules <module>` when you only need to replace the default import with
another rule module that is already available in the generated file's Rocq/Coq
environment:

```bash
linux-binary/symexec ... --CRules sll_C_Rules
```

This emits:

```coq
Import sll_C_Rules.
```

`--CRules` only emits `Import <module>.`; it does not add the module's
dependencies. If a custom rules module needs extra libraries, use
`--no-CRules` and write the imports explicitly in the annotated C file or an
included header:

```c
/*@ Import Coq Require Import critical_sll_lib */
/*@ Import Coq Import sll_C_Rules */
```

Many concurrent or project-specific examples use this manual form, with rule
modules such as `sll_C_Rules`, `sll_NC_Rules`, `sll_TC_Rules`,
`sll_CT_Rules`, or `Los_C_Rules`. For ordinary sequential examples that do not
need special rules, the default `naive_C_Rules` import is usually enough.

## Lean Generation

QCP can also emit Lean proof artifacts. Use `--lean-output-dir <dir>` to enable
Lean generation and let `symexec` derive the generated Lean file paths from
that directory. Use `--lean-logic-path <path>` when the generated Lean files
need a specific import prefix.

For example, to generate only Lean artifacts:

```bash
linux-binary/symexec \
  --input-file QCP_examples/path/to/example.c \
  --lean-output-dir Lean/examples/path/to/output \
  --lean-logic-path SimpleC.EE \
  --no-coq-gen
```

To generate both Rocq/Coq and Lean artifacts in one run, provide both output
directories and omit `--no-coq-gen`:

```bash
linux-binary/symexec \
  --input-file QCP_examples/path/to/example.c \
  --coq-output-dir Rocq/examples/path/to/output \
  --lean-output-dir Lean/examples/path/to/output
```

Use `--no-lean-gen` when you want to force a Rocq/Coq-only run even if a
wrapper or argument file would otherwise enable Lean generation. Generated Lean
files are checked with the Lake packages under `Lean/`.
