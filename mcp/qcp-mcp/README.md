# qcp-mcp

`qcp-mcp` is the MCP wrapper for the repository's QCP binary. It starts the
underlying `mcp` executable, keeps a session alive, and exposes tools such as
`load_target_file`, `check`, `step`, `symbolic`, `proof`, and `close`.

## Prerequisites

- Python 3.12+
- The repository `mcp` binary
  - Linux / WSL: `bin/linux/mcp`
  - Windows: `bin/windows/mcp.exe`

## Configuration

`qcp-mcp` resolves the backend binary in this order:

1. `QCP_MCP_BIN`
2. `QCP_MCP_CONFIG`
3. local `CONFIGURE`

The config file may contain either:

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/bin/linux/mcp
```

or:

```ini
QCP_MCP_BIN=D:/absolute/path/to/qcp-binary-democases/bin/windows/mcp.exe
```

If `QCP_MCP_BIN` is already set in the environment, you do not need to modify
`CONFIGURE`.

## Linux / WSL Setup

```bash
cd mcp/qcp-mcp
uv venv .venv
uv sync
```

Optional `CONFIGURE`:

```ini
QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/bin/linux/mcp
```

## Windows / PowerShell Setup

```powershell
Set-Location mcp\qcp-mcp
py -3 -m venv .venv-win
.\.venv-win\Scripts\python.exe -m pip install -e .
Set-Location ..\..
. .\scripts\setup-windows-mcp-env.ps1
```

The PowerShell setup script exports:

- `QCP_MCP_BIN`
- `QCP_MCP_PYTHON`
- `QCP_MCP_CONFIG`
- `COQC_EXE`
- `COQTOP_EXE`

Recommended Windows usage:

- Keep `qcp-mcp/CONFIGURE` available for Linux / WSL if needed.
- Use `QCP_MCP_BIN` from `setup-windows-mcp-env.ps1` for PowerShell.

## Smoke Test

Linux / WSL:

```bash
PYTHONPATH=$PWD/src QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/bin/linux/mcp \
  .venv/bin/python -m qcp_mcp.server
```

Windows:

```powershell
$env:QCP_MCP_BIN = 'D:\absolute\path\to\qcp-binary-democases\bin\windows\mcp.exe'
.\.venv-win\Scripts\python.exe -m qcp_mcp.server
```

To test actual tool behavior on Windows:

```powershell
@'
import asyncio, json
from qcp_mcp.server import initialize, check, symbolic, close

TARGET = r"D:\absolute\path\to\qcp-binary-democases\QCP_examples\QCP_demos_LLM\simple_arith\add.c"

async def main():
    await initialize(TARGET)
    chk = json.loads(await check(10))
    sym = json.loads(await symbolic(57))
    print("check:", chk["result"], chk["functionName"])
    print("symbolic:", sym["result"], sym["functionName"])
    print(await close())

asyncio.run(main())
'@ | .\mcp\qcp-mcp\.venv-win\Scripts\python.exe -
```

## MCP Client Configuration

### VS Code Copilot

Linux / WSL:

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
        "QCP_MCP_BIN": "/absolute/path/to/qcp-binary-democases/bin/linux/mcp"
      }
    }
  }
}
```

Windows:

```json
{
  "servers": {
    "qcp": {
      "type": "stdio",
      "command": "D:/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv-win/Scripts/python.exe",
      "args": [
        "-m",
        "qcp_mcp.server"
      ],
      "env": {
        "PYTHONPATH": "D:/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src",
        "QCP_MCP_BIN": "D:/absolute/path/to/qcp-binary-democases/bin/windows/mcp.exe"
      }
    }
  }
}
```

### Claude Code

Linux / WSL:

```bash
claude mcp add -s project qcp --env QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/bin/linux/mcp -- /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python -m qcp_mcp.server
```

Windows:

```powershell
claude mcp add -s project qcp --env QCP_MCP_BIN=D:/absolute/path/to/qcp-binary-democases/bin/windows/mcp.exe -- D:/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv-win/Scripts/python.exe -m qcp_mcp.server
```

### Codex

Linux / WSL:

```bash
codex mcp add qcp --env PYTHONPATH=/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src --env QCP_MCP_BIN=/absolute/path/to/qcp-binary-democases/bin/linux/mcp -- /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python -m qcp_mcp.server
```

Windows:

```powershell
codex mcp add qcp --env PYTHONPATH=D:/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src --env QCP_MCP_BIN=D:/absolute/path/to/qcp-binary-democases/bin/windows/mcp.exe -- D:/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv-win/Scripts/python.exe -m qcp_mcp.server
```
