param(
    [string]$TacticSource = '.lake/eta-opt/EtaCoefficient-original.lean',
    [string]$CertificateSource = '.lake/eta-opt/Certificates-original.lean',
    [switch]$PrepareOnly
)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
$taskOutput = Join-Path $taskRoot '.lake/eta-opt'
$taskUtf8 = New-Object Text.UTF8Encoding($false)
$taskOriginalCert = [IO.File]::ReadAllText((Join-Path $taskRoot $CertificateSource))
$taskOriginalTactic = [IO.File]::ReadAllText((Join-Path $taskRoot $TacticSource))
$taskCert = $taskOriginalCert.Replace('namespace WeightTwoCusps.EtaQuotient',
    "namespace WeightTwoCusps.EtaBaseline`n`nopen WeightTwoCusps.EtaQuotient")
$taskCert = $taskCert.Replace('end WeightTwoCusps.EtaQuotient', 'end WeightTwoCusps.EtaBaseline')
$taskTactic = $taskOriginalTactic.Replace('public import WeightTwoCusps.EtaQuotient.QExpansion.Certificates',
    'public import EtaBaselineCertificates')
$taskTactic = $taskTactic.Replace('WeightTwoCusps.Tactic', 'WeightTwoCusps.EtaBaselineTactic')
$taskTactic = $taskTactic.Replace('macro "eta_coeff"', 'macro "eta_coeff_baseline"')
# Qualify every cloned certificate declaration; coefficient formulas remain unchanged.
foreach ($taskMatch in [regex]::Matches($taskOriginalCert, '(?m)^(?:def|theorem)\s+([A-Za-z][A-Za-z0-9_]*)')) {
    $taskName = $taskMatch.Groups[1].Value
    $taskTactic = [regex]::Replace($taskTactic, "\b$taskName\b", "WeightTwoCusps.EtaBaseline.$taskName")
}
[IO.File]::WriteAllText((Join-Path $taskOutput 'EtaBaselineCertificates.lean'), $taskCert, $taskUtf8)
[IO.File]::WriteAllText((Join-Path $taskOutput 'EtaBaselineTactic.lean'), $taskTactic, $taskUtf8)
if ($PrepareOnly) { Write-Output 'Prepared isolated original implementation'; exit 0 }
$taskToolchain = [IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim()
$taskToolchainDir = $taskToolchain.Replace('/', '--').Replace(':', '---')
$taskLean = Join-Path $env:USERPROFILE ".elan/toolchains/$taskToolchainDir/bin/lean.exe"
$taskPaths = @($taskOutput, (Join-Path $taskRoot '.lake/build/lib/lean'))
$taskPaths += Get-ChildItem (Join-Path $taskRoot '.lake/packages') -Directory |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' }
$env:LEAN_PATH = $taskPaths -join ';'
$env:LEAN_NUM_THREADS = '2'
foreach ($taskModule in @('EtaBaselineCertificates', 'EtaBaselineTactic')) {
    & $taskLean "--root=$taskOutput" (Join-Path $taskOutput "$taskModule.lean") `
        '-o' (Join-Path $taskOutput "$taskModule.olean")
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    Write-Output "Built isolated $taskModule"
}
