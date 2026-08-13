param(
    [ValidateSet("build", "clean")]
    [string] $Task = "build",

    [string] $Lake = "lake",

    [ValidateRange(0, 10)]
    [int] $Retries = 2
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")

$localElanBin = Join-Path $env:USERPROFILE ".elan\bin"
if (Test-Path $localElanBin) {
    $env:PATH = "$localElanBin;$env:PATH"
}

$toolchainFile = Join-Path $repoRoot "lean-toolchain"
if (-not $env:ELAN_TOOLCHAIN -and (Test-Path $toolchainFile)) {
    $toolchain = (Get-Content $toolchainFile -Raw).Trim()
    if ($toolchain -match "v([0-9]+\.[0-9]+\.[0-9]+)$") {
        $localToolchain = "annotated-simplec-lean-$($Matches[1])"
        $elanCommand = Get-Command elan -ErrorAction SilentlyContinue
        if ($elanCommand) {
            $installedToolchains = & $elanCommand.Source toolchain list
            if ($installedToolchains -contains $localToolchain) {
                $env:ELAN_TOOLCHAIN = $localToolchain
            }
        }
    }
}

$lakeCommand = Get-Command $Lake -ErrorAction SilentlyContinue
if (-not $lakeCommand) {
    throw "Could not find '$Lake'. Install elan first, then reopen PowerShell or add '$localElanBin' to PATH."
}

$buildPlan = @(
    @{ Path = "compcert_lib"; Target = @() },
    @{ Path = "unifysl"; Target = @("Unifysl") },
    @{ Path = "auxlibs"; Target = @() },
    @{ Path = "sets"; Target = @() },
    @{ Path = "listlib"; Target = @() },
    @{ Path = "fixedpoints"; Target = @() },
    @{ Path = "SeparationLogic"; Target = @() },
    @{ Path = "MonadLib"; Target = @() },
    @{ Path = "examples"; Target = @() }
)

if ($Task -eq "clean") {
    [array]::Reverse($buildPlan)
}

foreach ($pkg in $buildPlan) {
    $pkgPath = Join-Path $repoRoot $pkg.Path
    if (-not (Test-Path $pkgPath)) {
        throw "Package directory not found: $pkgPath"
    }

    $attempt = 0
    while ($true) {
        $attempt += 1

        Push-Location $pkgPath
        try {
            if ($Task -eq "build") {
                Write-Host "==> lake build $($pkg.Path) $($pkg.Target -join ' ')"
                & $lakeCommand.Source build @($pkg.Target)
            } else {
                Write-Host "==> lake clean $($pkg.Path)"
                & $lakeCommand.Source clean
            }
            $exitCode = $LASTEXITCODE
        } finally {
            Pop-Location
        }

        if ($exitCode -eq 0) {
            break
        }

        if ($Task -eq "build" -and $attempt -le ($Retries + 1)) {
            Write-Warning "lake build failed in $($pkg.Path) with exit code $exitCode; retrying ($attempt/$Retries)."
            Start-Sleep -Seconds 2
            continue
        }

        throw "lake $Task failed in $($pkg.Path) with exit code $exitCode"
    }
}
