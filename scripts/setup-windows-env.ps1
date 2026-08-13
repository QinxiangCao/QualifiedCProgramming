param(
    [string]$RepoRoot = (Join-Path $PSScriptRoot "..")
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Import-RegisteredPathEntries {
    param(
        [string[]]$PreferredEntries = @(),
        [switch]$CurrentPathOnly
    )

    $entries = New-Object 'System.Collections.Generic.List[string]'
    $seen = New-Object 'System.Collections.Generic.HashSet[string]' `
        ([System.StringComparer]::OrdinalIgnoreCase)
    $pathValues = @(
        [string]::Join([System.IO.Path]::PathSeparator, $PreferredEntries),
        [Environment]::GetEnvironmentVariable("Path", [EnvironmentVariableTarget]::Process)
    )
    if (-not $CurrentPathOnly) {
        $pathValues += @(
            [Environment]::GetEnvironmentVariable("Path", [EnvironmentVariableTarget]::Machine),
            [Environment]::GetEnvironmentVariable("Path", [EnvironmentVariableTarget]::User)
        )
    }

    foreach ($pathValue in $pathValues) {
        if ([string]::IsNullOrWhiteSpace($pathValue)) {
            continue
        }
        $expanded = [Environment]::ExpandEnvironmentVariables($pathValue)
        foreach ($entryValue in $expanded.Split([System.IO.Path]::PathSeparator)) {
            $entry = $entryValue.Trim().Trim([char]34)
            if (-not [string]::IsNullOrWhiteSpace($entry) -and $seen.Add($entry)) {
                $entries.Add($entry)
            }
        }
    }
    $env:PATH = [string]::Join([System.IO.Path]::PathSeparator, $entries)
}

function Resolve-NativeExecutable {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Name,
        [string]$ConfiguredPath = ""
    )

    if (-not [string]::IsNullOrWhiteSpace($ConfiguredPath)) {
        $candidate = [System.IO.Path]::GetFullPath($ConfiguredPath)
        if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) {
            throw "Configured $Name executable was not found: $candidate"
        }
        if ([System.IO.Path]::GetExtension($candidate) -ine ".exe") {
            throw "Configured $Name must resolve to an .exe, not a command wrapper: $candidate"
        }
        return $candidate
    }

    $command = Get-Command $Name -CommandType Application -ErrorAction SilentlyContinue |
        Select-Object -First 1
    if ($null -eq $command) {
        throw (
            "Cannot find $Name in the current or registered PATH. " +
            "Install it, or set its explicit environment variable."
        )
    }
    $candidate = [System.IO.Path]::GetFullPath($command.Source)
    if ([System.IO.Path]::GetExtension($candidate) -ine ".exe") {
        throw "Discovered $Name is not an .exe: $candidate"
    }
    return $candidate
}

function Invoke-NativeText {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Executable,
        [Parameter(Mandatory = $true)]
        [string[]]$Arguments
    )

    $output = @(& $Executable @Arguments 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $rendered = $output -join [Environment]::NewLine
        throw (
            "Native command failed ($LASTEXITCODE): $Executable " +
            "$($Arguments -join ' ')`n$rendered"
        )
    }
    return ($output -join [Environment]::NewLine).Trim()
}

function Assert-ToolVersions {
    param(
        [Parameter(Mandatory = $true)][string]$Coqc,
        [Parameter(Mandatory = $true)][string]$Coqtop,
        [string]$Dune = "",
        [string]$MakeExe = ""
    )

    $coqcVersion = Invoke-NativeText -Executable $Coqc -Arguments @("--version")
    $coqtopVersion = Invoke-NativeText -Executable $Coqtop -Arguments @("--version")
    foreach ($toolVersion in @($coqcVersion, $coqtopVersion)) {
        if ($toolVersion -notmatch '(?im)\bversion\s+8\.20\.1\b') {
            throw "This repository requires Coq 8.20.1, but the executable reported:`n$toolVersion"
        }
    }

    $duneSelected = -not [string]::IsNullOrWhiteSpace($Dune)
    $makeSelected = -not [string]::IsNullOrWhiteSpace($MakeExe)
    if ($duneSelected -eq $makeSelected) {
        throw "Exactly one selected build executable must be validated."
    }
    if ($duneSelected) {
        $buildVersionText = Invoke-NativeText -Executable $Dune -Arguments @("--version")
        $duneVersionMatch = [regex]::Match($buildVersionText, '\d+\.\d+(?:\.\d+)?')
        if (-not $duneVersionMatch.Success) {
            throw "Cannot parse the Dune version from: $buildVersionText"
        }
        $duneVersion = [Version]$duneVersionMatch.Value
        if ($duneVersion -lt [Version]"3.16.1") {
            throw "This repository requires Dune 3.16.1 or newer, but found $duneVersion."
        }
    }
    else {
        $buildVersionText = Invoke-NativeText -Executable $MakeExe -Arguments @("--version")
        if ($buildVersionText -notmatch '(?im)^GNU Make\s+\d+') {
            throw "Makefile mode requires GNU Make, but the executable reported:`n$buildVersionText"
        }
    }
    return @($coqcVersion, $buildVersionText)
}

function Assert-UvManagedVenv {
    param(
        [Parameter(Mandatory = $true)][string]$Root,
        [Parameter(Mandatory = $true)][string]$Uv
    )

    $venvRoot = Join-Path $Root ".venv"
    if (-not (Test-Path -LiteralPath $venvRoot -PathType Container)) {
        return
    }
    $venvConfig = Join-Path $venvRoot "pyvenv.cfg"
    $venvPython = Join-Path $venvRoot "Scripts\python.exe"
    foreach ($path in @($venvConfig, $venvPython)) {
        if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
            throw "Existing .venv is incomplete: $path"
        }
    }

    $managedRootText = Invoke-NativeText -Executable $Uv -Arguments @("python", "dir")
    $managedRootLine = @(
        $managedRootText -split "`r?`n" |
            Where-Object { -not [string]::IsNullOrWhiteSpace($_) }
    )[-1]
    $managedRoot = [System.IO.Path]::GetFullPath($managedRootLine.Trim().Trim([char]34))
    $homeLine = Get-Content -LiteralPath $venvConfig |
        Where-Object { $_ -match '^\s*home\s*=' } |
        Select-Object -First 1
    if ($null -eq $homeLine) {
        throw "Existing .venv has no Python home in $venvConfig"
    }
    $pythonHomeValue = ($homeLine -replace '^\s*home\s*=\s*', '').Trim().Trim([char]34)
    $pythonHome = [System.IO.Path]::GetFullPath($pythonHomeValue)
    $managedPrefix = $managedRoot.TrimEnd('\', '/') + [System.IO.Path]::DirectorySeparatorChar
    if (-not $pythonHome.Equals($managedRoot, [StringComparison]::OrdinalIgnoreCase) -and
        -not $pythonHome.StartsWith($managedPrefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw (
            "Existing .venv does not use a uv-managed Python: $pythonHome. " +
            "Move or remove .venv, then recreate it with " +
            "uv sync --frozen --python 3.12."
        )
    }

    $pythonVersion = Invoke-NativeText -Executable $venvPython -Arguments @(
        "-c", "import sys; print(f'{sys.version_info.major}.{sys.version_info.minor}')"
    )
    if ($pythonVersion -ne "3.12") {
        throw "Existing .venv uses Python $pythonVersion; this repository requires Python 3.12."
    }
}

function Get-WindowsLongPathsEnabled {
    try {
        $value = [Microsoft.Win32.Registry]::LocalMachine.OpenSubKey(
            "SYSTEM\CurrentControlSet\Control\FileSystem"
        ).GetValue("LongPathsEnabled", 0)
        return ([int]$value -eq 1)
    }
    catch {
        return $false
    }
}

Import-RegisteredPathEntries

$repoRootPath = (Resolve-Path -LiteralPath $RepoRoot).Path
$useDune = Test-Path -LiteralPath (Join-Path $repoRootPath "_build") -PathType Container
$buildMode = if ($useDune) { "dune" } else { "makefile" }
$winBinaryDir = Join-Path $repoRootPath "win-binary"
$duneShim = Join-Path $repoRootPath "dune.cmd"
$fakeOcamlc = Join-Path $repoRootPath "tools\windows\fake-ocaml\bin\ocamlc.exe"
$fakeMakeConfig = Join-Path $repoRootPath "tools\windows\fake-ocaml\lib\ocaml\Makefile.config"

if ($useDune) {
    $requiredRepositoryFiles = @(
        $duneShim,
        $fakeOcamlc,
        $fakeMakeConfig,
        (Join-Path $winBinaryDir "symexec.exe"),
        (Join-Path $winBinaryDir "StrategyCheck.exe"),
        (Join-Path $winBinaryDir "lsp.exe")
    )
}
else {
    $requiredRepositoryFiles = @(
        (Join-Path $winBinaryDir "symexec.exe"),
        (Join-Path $winBinaryDir "StrategyCheck.exe"),
        (Join-Path $winBinaryDir "lsp.exe"),
        (Join-Path $repoRootPath "Rocq\Makefile")
    )
}
foreach ($path in $requiredRepositoryFiles) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Required repository file was not found: $path"
    }
}

$configuredCoqc = if (Test-Path Env:COQC_EXE) { $env:COQC_EXE } else { "" }
$configuredCoqtop = if (Test-Path Env:COQTOP_EXE) { $env:COQTOP_EXE } else { "" }
$configuredDune = if (Test-Path Env:DUNE_REAL) { $env:DUNE_REAL } else { "" }
$configuredCoqdep = if (Test-Path Env:COQDEP_EXE) { $env:COQDEP_EXE } else { "" }
$configuredMake = if (Test-Path Env:MAKE_EXE) { $env:MAKE_EXE } else { "" }
$configuredUv = if (Test-Path Env:UV_EXE) { $env:UV_EXE } else { "" }

$env:QCP_SYMEXEC_EXE = [System.IO.Path]::GetFullPath((Join-Path $winBinaryDir "symexec.exe"))
$env:QCP_STRATEGYCHECK_EXE = [System.IO.Path]::GetFullPath(
    (Join-Path $winBinaryDir "StrategyCheck.exe")
)
$env:QCP_LSP_EXE = [System.IO.Path]::GetFullPath((Join-Path $winBinaryDir "lsp.exe"))
$env:UV_EXE = Resolve-NativeExecutable -Name "uv.exe" -ConfiguredPath $configuredUv
$env:UV_PYTHON_PREFERENCE = "only-managed"
$env:COQC_EXE = Resolve-NativeExecutable -Name "coqc.exe" -ConfiguredPath $configuredCoqc
$env:COQTOP_EXE = Resolve-NativeExecutable -Name "coqtop.exe" -ConfiguredPath $configuredCoqtop
if ($useDune) {
    $env:DUNE_REAL = Resolve-NativeExecutable -Name "dune.exe" -ConfiguredPath $configuredDune
    $env:DUNE_EXE = $env:DUNE_REAL
    $versionOutput = Assert-ToolVersions `
        -Coqc $env:COQC_EXE `
        -Coqtop $env:COQTOP_EXE `
        -Dune $env:DUNE_REAL
}
else {
    if ([string]::IsNullOrWhiteSpace($configuredCoqdep)) {
        $coqdepBesideCoqc = Join-Path (Split-Path -Parent $env:COQC_EXE) "coqdep.exe"
        if (Test-Path -LiteralPath $coqdepBesideCoqc -PathType Leaf) {
            $configuredCoqdep = $coqdepBesideCoqc
        }
    }
    $env:COQDEP_EXE = Resolve-NativeExecutable -Name "coqdep.exe" -ConfiguredPath $configuredCoqdep
    $makeExecutableName = "make.exe"
    if ([string]::IsNullOrWhiteSpace($configuredMake)) {
        $makeCommand = Get-Command $makeExecutableName -CommandType Application -ErrorAction SilentlyContinue |
            Select-Object -First 1
        if ($null -eq $makeCommand) {
            $makeExecutableName = "mingw32-make.exe"
        }
    }
    $env:MAKE_EXE = Resolve-NativeExecutable -Name $makeExecutableName -ConfiguredPath $configuredMake
    $versionOutput = Assert-ToolVersions `
        -Coqc $env:COQC_EXE `
        -Coqtop $env:COQTOP_EXE `
        -MakeExe $env:MAKE_EXE
}
Assert-UvManagedVenv -Root $repoRootPath -Uv $env:UV_EXE
$longPathsEnabled = Get-WindowsLongPathsEnabled
if (-not $longPathsEnabled) {
    Write-Warning (
        "Windows LongPathsEnabled is not enabled. init-run will reject a target " +
        "if its projected verification path reaches a legacy 248-character " +
        "directory or 260-character file boundary."
    )
}
$preferredToolDirs = @(
    (Split-Path -Parent $env:COQC_EXE),
    (Split-Path -Parent $env:COQTOP_EXE)
)
if ($useDune) {
    $fakeOcamlBin = [System.IO.Path]::GetFullPath((Split-Path -Parent $fakeOcamlc))
    $fakeOcamlLib = [System.IO.Path]::GetFullPath((Split-Path -Parent $fakeMakeConfig))
    $preferredToolDirs = @($fakeOcamlBin) + $preferredToolDirs + @(
        (Split-Path -Parent $env:DUNE_REAL)
    )
    $env:OCAMLLIB = $fakeOcamlLib
    $env:CAMLLIB = $fakeOcamlLib
}
else {
    $preferredToolDirs += @(
        (Split-Path -Parent $env:COQDEP_EXE),
        (Split-Path -Parent $env:MAKE_EXE)
    )
}
Import-RegisteredPathEntries -PreferredEntries $preferredToolDirs -CurrentPathOnly

$codexCommand = Get-Command codex.exe -CommandType Application -ErrorAction SilentlyContinue |
    Select-Object -First 1
if ($null -ne $codexCommand) {
    $env:CODEX_EXE = [System.IO.Path]::GetFullPath($codexCommand.Source)
}

Write-Host "Configured Windows verification tools for this PowerShell process:"
Write-Host "  QCP_SYMEXEC_EXE=$env:QCP_SYMEXEC_EXE"
Write-Host "  QCP_STRATEGYCHECK_EXE=$env:QCP_STRATEGYCHECK_EXE"
Write-Host "  QCP_LSP_EXE=$env:QCP_LSP_EXE"
Write-Host "  UV_EXE=$env:UV_EXE"
Write-Host "  UV_PYTHON_PREFERENCE=$env:UV_PYTHON_PREFERENCE"
Write-Host "  COQC_EXE=$env:COQC_EXE"
Write-Host "  COQTOP_EXE=$env:COQTOP_EXE"
Write-Host "  BUILD_MODE=$buildMode"
if ($useDune) {
    Write-Host "  DUNE_REAL=$env:DUNE_REAL"
    Write-Host "  DUNE_EXE=$env:DUNE_EXE"
    Write-Host "  OCAMLLIB=$env:OCAMLLIB"
}
else {
    Write-Host "  COQDEP_EXE=$env:COQDEP_EXE"
    Write-Host "  MAKE_EXE=$env:MAKE_EXE"
}
Write-Host "  COQ_VERSION=$($versionOutput[0] -replace '[\r\n]+', ' ')"
if ($useDune) {
    Write-Host "  DUNE_VERSION=$($versionOutput[1] -replace '[\r\n]+', ' ')"
}
else {
    Write-Host "  MAKE_VERSION=$($versionOutput[1] -replace '[\r\n]+', ' ')"
}
Write-Host "  LONG_PATHS_ENABLED=$longPathsEnabled"
if (Test-Path Env:CODEX_EXE) {
    Write-Host "  CODEX_EXE=$env:CODEX_EXE"
}
