param(
    [ValidateSet('all', 'qcp-demos-llm', 'llm-bench')]
    [string]$Scope = 'all'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$manifest = Join-Path $PSScriptRoot 'lean-generation-inputs.txt'
$scratch = Join-Path ([IO.Path]::GetTempPath()) ('qcp-lean-' + [guid]::NewGuid().ToString('N'))
$null = New-Item -ItemType Directory -Path $scratch
$exitCode = 0
Push-Location $repoRoot
try {
    foreach ($line in Get-Content -LiteralPath $manifest) {
        if ([string]::IsNullOrWhiteSpace($line) -or $line.StartsWith('#')) { continue }
        $fields = $line.Split('|')
        if ($fields.Count -ne 4) { throw "Invalid generation input: $line" }
        $tool, $source, $relativeOutput, $stem = $fields
        $isQcp = $source.StartsWith('QCP_examples/QCP_demos_LLM/')
        if ($Scope -eq 'qcp-demos-llm' -and -not $isQcp) { continue }
        if ($Scope -eq 'llm-bench' -and $isQcp) { continue }
        $binary = Join-Path $repoRoot "win-binary/$tool.exe"
        if (-not (Test-Path -LiteralPath $binary -PathType Leaf)) { throw "Missing generator: $binary" }
        if (-not (Test-Path -LiteralPath $source -PathType Leaf)) { throw "Missing input: $source" }
        $sourceDirectory = $source.Substring(0, $source.LastIndexOf('/') + 1)
        $sourceNamespace = 'SimpleC.EE.' + $sourceDirectory.Substring('QCP_examples/'.Length).TrimEnd('/').Replace('/', '.')
        $outputNamespace = $relativeOutput.Replace('/', '.')
        $extension = [IO.Path]::GetExtension($source)
        $generatorArgs = @(
            "-I$sourceDirectory", '-slp', $sourceDirectory, $sourceNamespace,
            '-slp', 'QCP_examples/LLM_bench/', 'SimpleC.EE.LLM_bench',
            '-IQCP_examples/QCP_demos_LLM/', '-slp', 'QCP_examples/QCP_demos_LLM/', 'SimpleC.EE.QCP_demos_LLM',
            '-IQCP_examples/LLM_bench/Codeforces/',
            '-IQCP_examples/stdlib/', '-slp', 'QCP_examples/stdlib/', 'SimpleC.stdlib',
            "--input-file=$source",
            '--no-exec-info', '--no-coq-gen',
            "--lean-output-dir=$scratch", "--lean-logic-path=$outputNamespace"
        )
        if ($tool -eq 'symexec' -and $stem -ne [IO.Path]::GetFileNameWithoutExtension($source)) {
            $generatorArgs += "--input-file-name=$stem$extension"
        }
        Write-Host "Generating Lean: $source"
        & $binary @generatorArgs
        if ($LASTEXITCODE -ne 0) { $exitCode = $LASTEXITCODE; throw "Generator failed for $source (exit $exitCode)." }
        $generatedStem = if ($tool -eq 'StrategyCheck') { $stem + '_strategy' } else { $stem }
        foreach ($suffix in @('_goal.lean', '_goal_check.lean')) {
            if (-not (Test-Path -LiteralPath (Join-Path $scratch ($generatedStem + $suffix)))) {
                throw "Generator did not produce $generatedStem$suffix"
            }
        }
        $destination = Join-Path $repoRoot "Lean/examples/$relativeOutput"
        $null = New-Item -ItemType Directory -Force -Path $destination
        # Publish native VCs unchanged. The generator emits proof templates even
        # when proofs already exist, so keep the reviewed proofs at destination.
        foreach ($file in Get-ChildItem -LiteralPath $scratch -Filter '*.lean' -File) {
            $target = Join-Path $destination $file.Name
            if ($file.Name.EndsWith('_goal.lean') -or $file.Name.EndsWith('_goal_check.lean') -or -not (Test-Path -LiteralPath $target)) {
                Copy-Item -LiteralPath $file.FullName -Destination $target -Force
            }
        }
        Get-ChildItem -LiteralPath $scratch -File | Remove-Item -Force
    }
    Write-Host "Lean generation completed ($Scope)."
} catch {
    Write-Error -ErrorAction Continue $_
    if ($exitCode -eq 0) { $exitCode = 1 }
} finally {
    Pop-Location
    # Only remove files in this invocation's unique, flat output directory.
    Get-ChildItem -LiteralPath $scratch -File | Remove-Item -Force
    Remove-Item -LiteralPath $scratch
}
exit $exitCode
