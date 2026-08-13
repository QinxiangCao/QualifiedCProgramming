$repoRoot = Split-Path -Parent $PSScriptRoot
$leanRoot = Join-Path $repoRoot "Lean"
$setupScript = Join-Path $leanRoot "scripts\setup-windows.ps1"

if (-not (Test-Path -LiteralPath $setupScript -PathType Leaf)) {
    throw "Lean Windows setup script not found: $setupScript"
}

Push-Location $leanRoot
try {
    & $setupScript @args
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}
