<#
.SYNOPSIS
Removes Make-generated Rocq outputs on native Windows.
.DESCRIPTION
Without -Recurse, removes only the explicitly named files. With -Recurse,
walks the supplied directories and removes Coq build artifacts and caches.
Missing paths are harmless; other errors fail the Make recipe.
#>
[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [string[]] $Paths,
    [switch] $Recurse
)

$ErrorActionPreference = 'Stop'
$artifactPattern = '(^\..*\.aux$|\.(vo|vos|vok|glob)$|^\.(lia|nia|nra|csdp)\.cache$)'

foreach ($outputPath in $Paths) {
    if (-not (Test-Path -LiteralPath $outputPath)) {
        continue
    }
    if ($Recurse) {
        Get-ChildItem -LiteralPath $outputPath -Recurse -Force -File |
            Where-Object { $_.Name -match $artifactPattern } |
            ForEach-Object { Remove-Item -LiteralPath $_.FullName -Force }
    } else {
        # Never remove a directory in explicit-file mode.
        if (-not (Test-Path -LiteralPath $outputPath -PathType Leaf)) {
            throw "Expected an output file: $outputPath"
        }
        Remove-Item -LiteralPath $outputPath -Force
    }
}
