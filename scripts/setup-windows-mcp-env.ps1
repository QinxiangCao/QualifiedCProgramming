$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $PSScriptRoot

$qcpVenv = Join-Path $repoRoot "mcp\qcp-mcp\.venv-win"
$coqConfigure = Join-Path $repoRoot "SeparationLogic\CONFIGURE"

if (-not (Test-Path $qcpVenv)) {
    throw "Missing qcp-mcp Windows venv: $qcpVenv"
}

if (-not (Test-Path $coqConfigure)) {
    throw "Missing Coq CONFIGURE file: $coqConfigure"
}

function Get-ConfigureValue {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$Key
    )

    foreach ($line in Get-Content $Path) {
        if ($line -match "^\s*$Key\s*=\s*(.+?)\s*$") {
            return $Matches[1].Trim()
        }
    }

    return ""
}

$coqBin = Get-ConfigureValue -Path $coqConfigure -Key "COQBIN"
$coqSuf = Get-ConfigureValue -Path $coqConfigure -Key "SUF"

if (-not $coqBin) {
    throw "COQBIN is empty in $coqConfigure"
}

$coqcExe = Join-Path $coqBin ("coqc" + $coqSuf)
$coqtopExe = Join-Path $coqBin ("coqtop" + $coqSuf)
$qcpPython = Join-Path $qcpVenv "Scripts\python.exe"
$qcpBin = Join-Path $repoRoot "win-binary\mcp.exe"

$env:QCP_MCP_BIN = $qcpBin
$env:QCP_MCP_PYTHON = $qcpPython
$env:QCP_MCP_CONFIG = Join-Path $repoRoot "mcp\qcp-mcp\CONFIGURE"
$env:COQC_EXE = $coqcExe
$env:COQTOP_EXE = $coqtopExe

Write-Host "QCP_MCP_BIN=$env:QCP_MCP_BIN"
Write-Host "QCP_MCP_PYTHON=$env:QCP_MCP_PYTHON"
Write-Host "QCP_MCP_CONFIG=$env:QCP_MCP_CONFIG"
Write-Host "COQC_EXE=$env:COQC_EXE"
Write-Host "COQTOP_EXE=$env:COQTOP_EXE"
