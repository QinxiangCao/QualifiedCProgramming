$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$repoRoot = Split-Path -Parent $PSScriptRoot
$qcpVenv = Join-Path $repoRoot "mcp\qcp-mcp\.venv-win"
$qcpPython = Join-Path $qcpVenv "Scripts\python.exe"
$qcpBin = Join-Path $repoRoot "win-binary\mcp.exe"

foreach ($path in @($qcpPython, $qcpBin)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Required qcp-mcp file was not found: $path"
    }
}

function Resolve-McpRocqExecutable {
    param(
        [Parameter(Mandatory = $true)][string]$Name,
        [Parameter(Mandatory = $true)][string]$EnvironmentName
    )

    $configured = [Environment]::GetEnvironmentVariable($EnvironmentName)
    if (-not [string]::IsNullOrWhiteSpace($configured)) {
        $candidate = [System.IO.Path]::GetFullPath($configured)
        if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) {
            throw "Configured $EnvironmentName executable was not found: $candidate"
        }
        if ([System.IO.Path]::GetExtension($candidate) -ine ".exe") {
            throw "Configured $EnvironmentName must resolve to an .exe: $candidate"
        }
        return $candidate
    }
    $command = Get-Command $Name -CommandType Application -ErrorAction SilentlyContinue |
        Select-Object -First 1
    if ($null -eq $command) {
        throw "Cannot find $Name in PATH. Dot-source scripts\setup-windows-env.ps1 first."
    }
    $candidate = [System.IO.Path]::GetFullPath($command.Source)
    if ([System.IO.Path]::GetExtension($candidate) -ine ".exe") {
        throw "Discovered $Name is not an .exe: $candidate"
    }
    return $candidate
}

$env:QCP_MCP_BIN = [System.IO.Path]::GetFullPath($qcpBin)
$env:QCP_MCP_PYTHON = [System.IO.Path]::GetFullPath($qcpPython)
$env:QCP_MCP_CONFIG = [System.IO.Path]::GetFullPath((Join-Path $repoRoot "mcp\qcp-mcp\CONFIGURE"))
$env:COQC_EXE = Resolve-McpRocqExecutable -Name "coqc.exe" -EnvironmentName "COQC_EXE"
$env:COQTOP_EXE = Resolve-McpRocqExecutable -Name "coqtop.exe" -EnvironmentName "COQTOP_EXE"

Write-Host "QCP_MCP_BIN=$env:QCP_MCP_BIN"
Write-Host "QCP_MCP_PYTHON=$env:QCP_MCP_PYTHON"
Write-Host "QCP_MCP_CONFIG=$env:QCP_MCP_CONFIG"
Write-Host "COQC_EXE=$env:COQC_EXE"
Write-Host "COQTOP_EXE=$env:COQTOP_EXE"
