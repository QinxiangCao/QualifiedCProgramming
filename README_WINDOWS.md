# Windows Setup

This guide collects the Windows-specific parts that were previously mixed into the main [README](README.md).

## Local Environment Setup

### Prerequisites

- Rocq 8.20.1 (Coq 8.20.1)
- `make` compatible with your Windows environment
- PowerShell

Optional:

- `uv` for `qcp-mcp`

### Configure Rocq

Create both:

- `SeparationLogic/CONFIGURE`
- `SeparationLogic/unifysl/CONFIGURE`

with:

```ini
COQBIN = D:/path/to/Coq/bin/
SUF = .exe
```

`COQBIN` should point to the directory that contains `coqc.exe` and `coqtop.exe`.

### Initialize Repository Environment Variables

From the repository root, run:

```powershell
. .\scripts\setup-windows-env.ps1
```

This sets the Windows agent/tooling variables from repository-local paths:

- `QCP_SYMEXEC_EXE` -> `win-binary/symexec.exe`
- `QCP_STRATEGYCHECK_EXE` -> `win-binary/StrategyCheck.exe`
- `QCP_LSP_EXE` -> `win-binary/lsp.exe`
- `QCP_MCP_EXE` -> `win-binary/mcp.exe`
- `COQC_EXE` / `COQTOP_EXE` -> derived from `SeparationLogic/CONFIGURE` `COQBIN`
- `CODEX_EXE` -> filled when `codex.exe` is already discoverable

### Build Rocq Files

```powershell
Set-Location SeparationLogic\unifysl
make depend
make
Set-Location ..
make depend
make
```

## QIDE Extension

Set:

- `qide.lspBinPath` to `win-binary/lsp.exe`
- `qide.lspArg` as needed for your QCP options

## VS Code Coq Proof Extension

For Rocq/Coq proof interaction on Windows with Coq 8.20, use the repository-local `vscoq-2.2.3.vsix` extension together with the `vscoqtop.exe` binary shipped by the Coq Platform style Windows installation.

Why this setup:

- the Windows Coq 8.20 installation used in this repository provides `vscoqtop.exe`
- it does not provide `coq-lsp.exe`
- the verified working editor setup in this repository is `VsCoq 2.2.3`

### Install the Extension

From VS Code:

- open the command palette
- run `Extensions: Install from VSIX...`
- choose `vscoq-2.2.3.vsix` from the repository root

If you previously installed other Coq-focused VS Code extensions, disable them for this workspace before testing `VsCoq 2.2.3`:

- `ejgallego.coq-lsp`
- `rocq-prover.vsrocq`

### Workspace Settings

Add or update the following settings in your workspace `.vscode/settings.json`:

```json
{
  "vscoq.path": "D:/Coq8.20/bin/vscoqtop.exe",
  "vscoq.args": [],
  "vscoq-language-server.trace.server": "off",
  "vscoq.proof.mode": 0,
  "vscoq.proof.pointInterpretationMode": 1,
  "vscoq.proof.delegation": "None",
  "vscoq.proof.display-buttons": false
}
```

The `vscoq.path` value above is an example path. Replace it with the path to `vscoqtop.exe` in your own Coq installation.

`vscoq.proof.mode: 0` means manual proof checking.

### Expected Binary Layout

The relevant Coq executables for this setup are:

- `D:/Coq8.20/bin/coqc.exe`
- `D:/Coq8.20/bin/coqtop.exe`
- `D:/Coq8.20/bin/vscoqtop.exe`

After installing the VSIX, reload the VS Code window and open a `.v` file to verify that the proof view and navigation commands are active.

## QCP Command-Line Tool

Use `win-binary/symexec.exe` directly, or run all examples with the native Windows script. It can be launched from either shell without Bash:

```cmd
run-example-windows.cmd
```

```powershell
.\run-example-windows.cmd
```

## MCP Setup

### Install `uv`

```powershell
powershell -ExecutionPolicy ByPass -c "irm https://astral.sh/uv/install.ps1 | iex"
```

### Configure `qcp-mcp`

```powershell
Set-Location mcp\qcp-mcp
py -3 -m venv .venv-win
.\.venv-win\Scripts\python.exe -m pip install -e .
```

Then initialize the Windows-side MCP environment from the repository root:

```powershell
. .\scripts\setup-windows-mcp-env.ps1
```

This exports:

- `QCP_MCP_BIN` -> `win-binary/mcp.exe`
- `QCP_MCP_PYTHON` -> `mcp/qcp-mcp/.venv-win/Scripts/python.exe`
- `COQC_EXE` -> derived from `SeparationLogic/CONFIGURE`
- `COQTOP_EXE` -> derived from `SeparationLogic/CONFIGURE`

You do not need to overwrite `mcp/qcp-mcp/CONFIGURE` for PowerShell usage. Keeping that file available for Linux/WSL is fine because the Windows script sets `QCP_MCP_BIN` explicitly.

### Test `qcp-mcp`

```powershell
@'
import asyncio, json
from qcp_mcp.server import initialize, check, symbolic, close

TARGET = r"absolute\path\to\qcp-binary-democases\QCP_examples\QCP_demos_LLM\simple_arith\add.c"

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

### VS Code Copilot MCP Example

```json
{
  "servers": {
    "qcp": {
      "type": "stdio",
      "command": "absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv-win/Scripts/python.exe",
      "args": [
        "-m",
        "qcp_mcp.server"
      ],
      "env": {
        "PYTHONPATH": "absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src",
        "QCP_MCP_BIN": "absolute/path/to/qcp-binary-democases/win-binary/mcp.exe"
      }
    }
  }
}
```

### Claude Code

```powershell
claude mcp add -s project qcp --env QCP_MCP_BIN=absolute/path/to/qcp-binary-democases/win-binary/mcp.exe -- absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv-win/Scripts/python.exe -m qcp_mcp.server
```

### Codex

```powershell
codex mcp add qcp --env PYTHONPATH=absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/src --env QCP_MCP_BIN=absolute/path/to/qcp-binary-democases/win-binary/mcp.exe -- absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv-win/Scripts/python.exe -m qcp_mcp.server
```

## Coq Proof Workflow

On Windows, the recommended proof workflow is still direct `coqtop` / `coqc` usage from the Coq installation configured in `SeparationLogic/CONFIGURE`.

- Use `qcp-mcp` only for QCP symbolic execution related MCP tasks.
- Use `coqc.exe` and `coqtop.exe` for Rocq/Coq proof compilation and interaction.

For agent-specific Windows execution rules, see [AGENTS_WIN.md](AGENTS_WIN.md).
