# MCP Setup

MCP setup is optional. Configure it only if you want an MCP-capable editor or
agent to call QCP or Rocq tools.

This repository has two MCP integrations:

- `qcp-mcp`: wraps the repository's QCP binary for annotated C and symbolic
  execution workflows.
- `rocq-mcp`: exposes Rocq/Coq proof tooling. This is useful only after the
  Rocq/Coq backend is installed.

All `/absolute/path/to/...` strings below are placeholders. Replace them with
the real QCP checkout path.

## Install `uv`

Linux/macOS:

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
export PATH="$HOME/.local/bin:$PATH"
uv --version
```

Windows PowerShell:

```powershell
powershell -ExecutionPolicy ByPass -c "irm https://astral.sh/uv/install.ps1 | iex"
$env:Path = "$env:USERPROFILE\.local\bin;$env:Path"
uv --version
```

## Configure `qcp-mcp`

Linux/macOS:

```bash
cd mcp/qcp-mcp
uv sync --python 3.12
cd ../..
```

Set `mcp/qcp-mcp/CONFIGURE` to the QCP `mcp` binary for your platform:

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/linux-binary/mcp
```

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/mac-arm64-binary/mcp
```

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/mac-x86-64-binary/mcp
```

Windows PowerShell:

```powershell
cd mcp\qcp-mcp
uv venv --python 3.12 .venv-win
uv pip install --python .venv-win\Scripts\python.exe -e .
cd ..\..

$env:QCP_MCP_BIN = (Resolve-Path .\win-binary\mcp.exe).Path
$env:QCP_MCP_PYTHON = (Resolve-Path .\mcp\qcp-mcp\.venv-win\Scripts\python.exe).Path
```

For persistent Windows agent/tooling environment variables, see
[`../AGENTS_WIN.md`](../AGENTS_WIN.md).

## Configure `rocq-mcp`

This is optional and applies only after the Rocq/Coq backend has been installed.
It is not part of the Lean-only setup.

Linux/macOS:

```bash
eval $(opam env --switch=qcp-rocq)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install -y coq-lsp
pet --version
```

Run `opam repo add` only once for this switch. The URL is an opam repository
endpoint rather than a normal web page, so validate it with `opam update`, not
by opening the root URL in a browser.

Then install the MCP package:

```bash
cd mcp/rocq-mcp
uv tool install .
cd ../..
command -v rocq-mcp
```

For Windows, this document covers `qcp-mcp`. Use `rocq-mcp` there only if you
already have a working Windows Rocq/Coq MCP installation.

## VS Code Copilot MCP Example

Linux:

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

macOS uses the same shape as Linux, with the macOS `QCP_MCP_BIN` path in
`mcp/qcp-mcp/CONFIGURE`.

Windows:

```json
{
  "servers": {
    "qcp": {
      "type": "stdio",
      "command": "D:/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv-win/Scripts/python.exe",
      "args": ["-m", "qcp_mcp.server"],
      "env": {
        "PYTHONPATH": "D:/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src",
        "QCP_MCP_BIN": "D:/absolute/path/to/qcp-binary-democases/win-binary/mcp.exe"
      }
    }
  }
}
```

## Claude Code

Linux:

```bash
claude mcp add -s project qcp --env QCP_MCP_CONFIG=/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/CONFIGURE -- /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python -m qcp_mcp.server
claude mcp add -s project rocq-mcp -- rocq-mcp
```

macOS uses the same commands as Linux. Claude's config directory is:

```text
~/Library/Application Support/Claude/
```

Linux config directory:

```text
~/.config/claude/
```

## Codex

Linux:

```bash
codex mcp add qcp --env PYTHONPATH=/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src --env QCP_MCP_CONFIG=/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/CONFIGURE -- /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python -m qcp_mcp.server
codex mcp add rocq-mcp -- rocq-mcp
```

Config file:

```text
~/.codex/config.toml
```
