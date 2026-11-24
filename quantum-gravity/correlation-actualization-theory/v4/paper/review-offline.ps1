# Windows x64 entry point. Uses the interpreter and wheels shipped with this release.
[CmdletBinding()]
param(
    [ValidateSet('check','quick','numerical','lean','study')][string]$Action = 'check',
    [string[]]$Names = @(),
    [string]$Cache = (Join-Path $PSScriptRoot '.review-cache')
)
$ErrorActionPreference = 'Stop'
$cacheRoot = [System.IO.Path]::GetFullPath($Cache)
$runtimeRoot = Join-Path $cacheRoot 'python-3.14.7-win64'
$distributionRoot = Join-Path $PSScriptRoot 'evidence/python-win64'
$distributionList = Get-Content -Raw -Encoding UTF8 -LiteralPath (Join-Path $distributionRoot 'distributions.json') | ConvertFrom-Json
$interpreter = $distributionList | Where-Object { $_.package -eq 'CPython' }
$zipFile = Join-Path $distributionRoot $interpreter.filename
if ((Get-FileHash -LiteralPath $zipFile -Algorithm SHA256).Hash.ToLowerInvariant() -ne $interpreter.sha256) {
    throw 'CPython archive digest does not match the release.'
}
$null = [System.IO.Directory]::CreateDirectory($runtimeRoot)
$exe = Join-Path $runtimeRoot 'python.exe'
if (-not (Test-Path -LiteralPath $exe)) {
    Add-Type -AssemblyName System.IO.Compression.FileSystem
    [System.IO.Compression.ZipFile]::ExtractToDirectory($zipFile, $runtimeRoot)
}
& $exe (Join-Path $PSScriptRoot 'portable_packages.py') $distributionRoot $runtimeRoot
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& $exe -B (Join-Path $PSScriptRoot 'review.py') $Action @Names '--cache' $cacheRoot
exit $LASTEXITCODE

