param(
    [switch] $ManualFallback
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
$toolchain = (Get-Content (Join-Path $repoRoot "lean-toolchain") -Raw).Trim()
$version = $toolchain
if ($toolchain -match "v([0-9]+\.[0-9]+\.[0-9]+)$") {
    $version = $Matches[1]
}

$elanBin = Join-Path $env:USERPROFILE ".elan\bin"
$env:PATH = "$elanBin;$env:PATH"

function Invoke-WithTimeout {
    param(
        [string] $FilePath,
        [string[]] $ArgumentList = @(),
        [int] $TimeoutSeconds = 30
    )

    $stamp = [Guid]::NewGuid().ToString("N")
    $stdout = Join-Path $env:TEMP "codex-$stamp.out"
    $stderr = Join-Path $env:TEMP "codex-$stamp.err"
    $process = Start-Process `
        -FilePath $FilePath `
        -ArgumentList $ArgumentList `
        -NoNewWindow `
        -PassThru `
        -RedirectStandardOutput $stdout `
        -RedirectStandardError $stderr

    if (-not $process.WaitForExit($TimeoutSeconds * 1000)) {
        Stop-Process -Id $process.Id -Force
        Write-Host "$FilePath $($ArgumentList -join ' ') timed out after $TimeoutSeconds seconds."
        return $false
    }

    if (Test-Path $stdout) {
        $stdoutText = Get-Content $stdout -Raw
        if ($stdoutText) {
            Write-Host $stdoutText.TrimEnd()
        }
    }
    if (Test-Path $stderr) {
        $stderrText = Get-Content $stderr -Raw
        if ($stderrText) {
            Write-Host $stderrText.TrimEnd()
        }
    }

    return ($process.ExitCode -eq 0)
}

function Test-LeanToolchain {
    $leanCommand = Get-Command lean -ErrorAction SilentlyContinue
    $lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
    if (-not $leanCommand -or -not $lakeCommand) {
        return $false
    }

    [bool] $leanOk = Invoke-WithTimeout -FilePath $leanCommand.Source -ArgumentList @("--version")
    if (-not $leanOk) {
        return $false
    }

    [bool] $lakeOk = Invoke-WithTimeout -FilePath $lakeCommand.Source -ArgumentList @("--version")
    return $lakeOk
}

if (-not (Get-Command elan -ErrorAction SilentlyContinue)) {
    $installer = Join-Path $env:TEMP "elan-init.ps1"
    Invoke-WebRequest -Uri "https://elan.lean-lang.org/elan-init.ps1" -UseBasicParsing -OutFile $installer
    & $installer -NoPrompt 1 -DefaultToolchain $toolchain
    $env:PATH = "$elanBin;$env:PATH"
}

if (-not $ManualFallback) {
    & elan --version
    Write-Host "elan is ready. The first lake/lean command will download $toolchain if needed."
    Write-Host "If that download fails with CRYPT_E_REVOCATION_OFFLINE, rerun:"
    Write-Host "  .\scripts\setup-windows.ps1 -ManualFallback"
    exit 0
}

$manualRoot = Join-Path $env:USERPROFILE ".elan\manual"
$archive = Join-Path $env:TEMP "lean-$version-windows.tar.zst"
$downloadUrl = "https://github.com/leanprover/lean4/releases/download/v$version/lean-$version-windows.tar.zst"
$toolchainDir = Join-Path $manualRoot "lean-$version-windows"
$localName = "annotated-simplec-lean-$version"

New-Item -ItemType Directory -Force $manualRoot | Out-Null

Write-Host "Downloading $downloadUrl"
& curl.exe -L --ssl-no-revoke --retry 20 --retry-all-errors -C - -o $archive $downloadUrl
if ($LASTEXITCODE -ne 0) {
    throw "curl failed with exit code $LASTEXITCODE"
}

Write-Host "Extracting $archive"
Push-Location $manualRoot
try {
    & tar -xf $archive
    if ($LASTEXITCODE -ne 0) {
        throw "tar failed with exit code $LASTEXITCODE"
    }
} finally {
    Pop-Location
}

if (-not (Test-Path (Join-Path $toolchainDir "bin\lean.exe"))) {
    throw "Extracted toolchain does not contain bin\lean.exe: $toolchainDir"
}

& elan toolchain link $localName $toolchainDir
if ($LASTEXITCODE -ne 0) {
    throw "elan toolchain link failed with exit code $LASTEXITCODE"
}

Push-Location $repoRoot
try {
    & elan override set $localName
    if ($LASTEXITCODE -ne 0) {
        throw "elan override set failed with exit code $LASTEXITCODE"
    }
} finally {
    Pop-Location
}

if (-not (Test-LeanToolchain)) {
    throw "Lean toolchain setup finished, but lean/lake still failed to run."
}

Write-Host "Lean toolchain is ready."
