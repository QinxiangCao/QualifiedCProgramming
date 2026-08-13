param(
    [ValidateSet("build", "clean")]
    [string] $Task = "build",

    [string] $Lake = "lake",

    [int] $Retries = 2
)

$repoRoot = Split-Path -Parent $PSScriptRoot
$leanRoot = Join-Path $repoRoot "Lean"
$buildScript = Join-Path $leanRoot "scripts\build.ps1"

if (-not (Test-Path -LiteralPath $buildScript -PathType Leaf)) {
    throw "Lean build script not found: $buildScript"
}

Push-Location $leanRoot
try {
    & $buildScript -Task $Task -Lake $Lake -Retries $Retries
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}
