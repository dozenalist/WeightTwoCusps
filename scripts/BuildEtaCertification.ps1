param([switch]$Certificates, [switch]$Packed, [switch]$Oldforms)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
$taskToolchain = [IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim()
$taskToolchainDir = $taskToolchain.Replace('/', '--').Replace(':', '---')
$taskLean = Join-Path $env:USERPROFILE ".elan/toolchains/$taskToolchainDir/bin/lean.exe"
$taskPaths = @((Join-Path $taskRoot '.lake/build/lib/lean'))
$taskPaths += Get-ChildItem (Join-Path $taskRoot '.lake/packages') -Directory |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' }
$env:LEAN_PATH = $taskPaths -join ';'
$env:LEAN_NUM_THREADS = '2'
$taskModules = @()
if ($Certificates) { $taskModules += 'WeightTwoCusps/EtaQuotient/QExpansion/Certificates' }
if ($Packed) { $taskModules += 'WeightTwoCusps/EtaQuotient/QExpansion/PackedCertificates' }
if ($Oldforms) { $taskModules += 'WeightTwoCusps/Oldforms/QExpansion' }
$taskModules += 'WeightTwoCusps/Tactic/EtaCoefficient'
foreach ($taskModule in $taskModules) {
    $taskWatch = [Diagnostics.Stopwatch]::StartNew()
    & $taskLean "--root=$taskRoot" '-DrelaxedAutoImplicit=false' '-DmaxSynthPendingDepth=3' `
        '-o' ".lake/build/lib/lean/$taskModule.olean" `
        '-i' ".lake/build/lib/lean/$taskModule.ilean" "$taskModule.lean"
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    Write-Output "$taskModule checked in $($taskWatch.Elapsed.TotalSeconds) seconds"
}
