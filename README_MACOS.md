# macOS Setup

This guide collects the macOS-specific parts that were previously mixed into the main [README](README.md).

## Local Environment Setup

### Prerequisites

- Rocq 8.20.1 (Coq 8.20.1)
- `make`

Optional:

- `uv` for `qcp-mcp` / `rocq-mcp`
- `opam` + `coq-lsp` for `rocq-mcp` interactive tooling

### Choose the Correct QCP Binary Directory

- Apple Silicon: `mac-arm64-binary/`
- Intel Mac: `mac-x86-64-binary/`

You can check with:

```bash
uname -m
```

### Configure Rocq

If you prefer an explicit `CONFIGURE`, create both:

- `SeparationLogic/CONFIGURE`
- `SeparationLogic/unifysl/CONFIGURE`

with:

```ini
COQBIN = /absolute/path/to/coq/bin/
```

### Rocq Installation

Homebrew example:

```bash
brew install opam
opam init -y
eval $(opam env)
opam install coq.8.20.1
```

### Build Rocq Files

In `SeparationLogic`, the default `make` target is `core`, so it does not build the generated files under `SeparationLogic/examples`. `make depend` refreshes dependencies for all core and example files. If you need the full build, including all examples, run `make all` after `make depend`.

```bash
cd SeparationLogic/unifysl
make depend && make
cd ..

# Core libraries only, because the default target is core
make depend && make

# Full build, including all generated examples
make depend && make all
```

## QIDE Extension

Set `qide.lspBinPath` to:

- `mac-arm64-binary/lsp` on Apple Silicon
- `mac-x86-64-binary/lsp` on Intel Mac

## QCP Command-Line Tool

Use the matching `symexec` binary from your macOS directory.

## MCP Setup

### Install `uv`

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

### Configure `qcp-mcp`

```bash
cd mcp/qcp-mcp
uv venv .venv
uv sync
```

Set `mcp/qcp-mcp/CONFIGURE` to one of:

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/mac-arm64-binary/mcp
```

or:

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/mac-x86-64-binary/mcp
```

### Configure `rocq-mcp`

```bash
brew install opam
opam init -y
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq-lsp
pet --version
```

Then install the MCP package:

```bash
cd mcp/rocq-mcp
uv tool install ".[interactive]"
```

### VS Code Copilot MCP Example

```json
{
  "servers": {
    "qcp": {
      "type": "stdio",
      "command": "/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python",
      "args": [
        "-m",
        "qcp_mcp.server"
      ],
      "env": {
        "PYTHONPATH": "/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src",
        "QCP_MCP_CONFIG": "/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/CONFIGURE"
      }
    },
    "rocq-mcp": {
      "type": "stdio",
      "command": "rocq-mcp",
      "env": {
        "ROCQ_WORKSPACE": "${workspaceFolder}"
      }
    }
  }
}
```

### Claude Code

```bash
claude mcp add -s project qcp -- /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/server.py
claude mcp add -s project rocq-mcp -- rocq-mcp
```

Config directory:

- `~/Library/Application Support/Claude/`
