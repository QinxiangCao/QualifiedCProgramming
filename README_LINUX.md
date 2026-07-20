# Linux Setup

This guide collects the Linux-specific parts that were previously mixed into the main [README](README.md).

## Local Environment Setup

### Prerequisites

- Rocq 8.20.1 (Coq 8.20.1), recommended with OCaml 4.14.1
- `make`

Optional:

- `uv` for `qcp-mcp` / `rocq-mcp`
- `opam` + `coq-lsp` for `rocq-mcp` interactive tooling

### Rocq Installation

We recommend installing Rocq 8.20.1 via `opam`:

```bash
sudo apt update
sudo apt install -y opam
opam init
eval $(opam env)
opam install coq.8.20.1
```

With this setup:

- you usually do not need `SeparationLogic/CONFIGURE`
- you can use the VS Code `vsrocq` extension directly

If you prefer an explicit `CONFIGURE`, create both:

- `SeparationLogic/CONFIGURE`
- `SeparationLogic/unifysl/CONFIGURE`

with:

```ini
COQBIN = /absolute/path/to/coq/bin/
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

Set:

- `qide.lspBinPath` to `linux-binary/lsp`
- `qide.lspArg` as needed for your QCP options

## QCP Command-Line Tool

Use `linux-binary/symexec` directly, or refer to:

- `run-example-linux.sh`

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

Set `mcp/qcp-mcp/CONFIGURE` to:

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/linux-binary/mcp
```

### Configure `rocq-mcp`

```bash
sudo apt update
sudo apt install -y opam bubblewrap
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

- `~/.config/claude/`

### Codex

```bash
codex mcp add qcp --env PYTHONPATH=/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src --env QCP_MCP_CONFIG=/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/CONFIGURE -- /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python -m qcp_mcp.server
codex mcp add rocq-mcp -- rocq-mcp
```

Config file:

- `~/.codex/config.toml`
