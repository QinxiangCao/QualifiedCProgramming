param(
    [string]$RepoRoot = (Join-Path $PSScriptRoot "..")
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Get-ConfigureValue {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Path,
        [Parameter(Mandatory = $true)]
        [string]$Key
    )

    foreach ($line in Get-Content -LiteralPath $Path) {
        if ($line -match '^\s*#') {
            continue
        }

        if ($line -match "^\s*$Key\s*=\s*(.+?)\s*$") {
            return $matches[1].Trim().Trim("'`"")
        }
    }

    throw "Missing '$Key' in '$Path'."
}

$repoRootPath = (Resolve-Path -LiteralPath $RepoRoot).Path
$winBinaryDir = Join-Path $repoRootPath "win-binary"
$configurePath = Join-Path $repoRootPath "SeparationLogic\CONFIGURE"

if (-not (Test-Path -LiteralPath $configurePath)) {
    throw "Missing CONFIGURE file: $configurePath"
}

$coqBin = Get-ConfigureValue -Path $configurePath -Key "COQBIN"
if (-not [System.IO.Path]::IsPathRooted($coqBin)) {
    $coqBin = Join-Path (Split-Path -Parent $configurePath) $coqBin
}
$coqBin = [System.IO.Path]::GetFullPath($coqBin).TrimEnd('\', '/')

$env:QCP_SYMEXEC_EXE = (Join-Path $winBinaryDir "symexec.exe")
$env:QCP_STRATEGYCHECK_EXE = (Join-Path $winBinaryDir "StrategyCheck.exe")
$env:QCP_LSP_EXE = (Join-Path $winBinaryDir "lsp.exe")
$env:QCP_MCP_EXE = (Join-Path $winBinaryDir "mcp.exe")
$env:COQC_EXE = (Join-Path $coqBin "coqc.exe")
$env:COQTOP_EXE = (Join-Path $coqBin "coqtop.exe")

$requiredExecutables = @(
    $env:QCP_SYMEXEC_EXE,
    $env:QCP_STRATEGYCHECK_EXE,
    $env:QCP_LSP_EXE,
    $env:QCP_MCP_EXE,
    $env:COQC_EXE,
    $env:COQTOP_EXE
)

foreach ($exe in $requiredExecutables) {
    if (-not (Test-Path -LiteralPath $exe)) {
        throw "Expected executable not found: $exe"
    }
}

$codexCommand = Get-Command codex.exe -ErrorAction SilentlyContinue
if ($null -ne $codexCommand) {
    $env:CODEX_EXE = $codexCommand.Source
}

Write-Host "Configured Windows tool environment variables:"
Write-Host "  QCP_SYMEXEC_EXE=$env:QCP_SYMEXEC_EXE"
Write-Host "  QCP_STRATEGYCHECK_EXE=$env:QCP_STRATEGYCHECK_EXE"
Write-Host "  QCP_LSP_EXE=$env:QCP_LSP_EXE"
Write-Host "  QCP_MCP_EXE=$env:QCP_MCP_EXE"
Write-Host "  COQC_EXE=$env:COQC_EXE"
Write-Host "  COQTOP_EXE=$env:COQTOP_EXE"
if ($env:CODEX_EXE) {
    Write-Host "  CODEX_EXE=$env:CODEX_EXE"
}
