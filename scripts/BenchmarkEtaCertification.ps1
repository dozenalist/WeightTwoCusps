param(
    [string]$Label = 'baseline',
    [int]$Count = 50,
    [int]$Repeats = 1,
    [string]$Cases = 'complex462,simple462,heavy42,dilated462',
    [switch]$ArithmeticCount,
    [string]$TacticModule = 'WeightTwoCusps.Tactic.EtaCoefficient',
    [string]$TacticName = 'eta_coeff',
    [switch]$PrepareOnly
)

$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
$taskOutput = Join-Path $taskRoot '.lake/eta-opt'
[IO.Directory]::CreateDirectory($taskOutput) | Out-Null
$taskUtf8 = New-Object Text.UTF8Encoding($false)
$taskTimerSource = @'
module
public meta import Lean.Elab.Command
public meta section
initialize etaBenchStarted : IO.Ref Nat ← IO.mkRef 0
elab "eta_bench_begin" : command => do
  IO.eprintln "ETA_BENCH_BEGIN"
  etaBenchStarted.set (← IO.monoNanosNow)
elab "eta_bench_end" label:str : command => do
  let elapsed := (← IO.monoNanosNow) - (← etaBenchStarted.get)
  IO.println s!"ETA_BENCH {label.getString} {elapsed}"
'@
$taskTimerInput = Join-Path $taskOutput 'EtaBenchTimer.lean'
$taskTimerChanged = !(Test-Path -LiteralPath $taskTimerInput) -or
    [IO.File]::ReadAllText($taskTimerInput) -ne $taskTimerSource
[IO.File]::WriteAllText($taskTimerInput, $taskTimerSource, $taskUtf8)
$taskCases = @(
    @{ Name='complex462'; Level=462; Factors=@{1=-2;2=3;3=1;6=-1;7=3;11=2;14=-2;21=-1;22=-1;33=-1;42=1;66=1;77=-1;154=2;231=1;462=-1} },
    @{ Name='simple462'; Level=462; Factors=@{1=-1;2=1;3=1;11=2;21=2;22=-1;42=-1;77=1;231=-1;462=1} },
    @{ Name='heavy42'; Level=42; Factors=@{1=-2;2=4;3=1;6=-1;7=4;14=-2;21=-1;42=1} },
    @{ Name='dilated462'; Level=462; Factors=@{7=-1;11=3;14=1;21=3;22=-1;33=-1;42=-1;66=1} },
    @{ Name='tau'; Level=1; Factors=@{1=24} },
    @{ Name='theta'; Level=4; Factors=@{1=-8;2=20;4=-8} },
    @{ Name='eleven'; Level=11; Factors=@{1=2;11=2} },
    @{ Name='signed15'; Level=15; Factors=@{1=-1;3=5;5=5;15=-1} }
)
$taskSelected = $Cases.Split(',')
$taskCountTerm = if ($ArithmeticCount) { "($($Count - 1) / 1 + 1)" } else { "$Count" }
$taskSource = @'
module
public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient
public meta import EtaBenchTimer

set_option Elab.async false
set_option maxRecDepth 4096
open WeightTwoCusps UpperHalfPlane
public section
'@
$taskSource = $taskSource.Replace('public import WeightTwoCusps.Tactic.EtaCoefficient',
    "public import $TacticModule")
foreach ($taskCase in $taskCases) {
    if ($taskCase.Name -notin $taskSelected) { continue }
    $taskSum = 0
    $taskEntries = @()
    $taskUnit = New-Object 'System.Numerics.BigInteger[]' $Count
    $taskUnit[0] = 1
    foreach ($taskM in @($taskCase.Factors.Keys | Sort-Object)) {
        $taskExponent = $taskCase.Factors[$taskM]
        $taskSum += $taskM * $taskExponent
        $taskEntries += "$($taskM - 1) => $taskExponent"
        for ($taskK = $taskM; $taskK -lt $Count; $taskK += $taskM) {
            for ($taskPower = 0; $taskPower -lt [Math]::Abs($taskExponent); $taskPower++) {
                if ($taskExponent -gt 0) {
                    for ($taskN = $Count - 1; $taskN -ge $taskK; $taskN--) {
                        $taskUnit[$taskN] -= $taskUnit[$taskN - $taskK]
                    }
                } else {
                    for ($taskN = $taskK; $taskN -lt $Count; $taskN++) {
                        $taskUnit[$taskN] += $taskUnit[$taskN - $taskK]
                    }
                }
            }
        }
    }
    if ($taskSum -lt 0 -or $taskSum % 24 -ne 0) { throw 'Unsupported infinity sum' }
    $taskOrder = [int]($taskSum / 24)
    $taskValues = for ($taskN = 0; $taskN -lt $Count; $taskN++) {
        if ($taskN -lt $taskOrder) { '0' } else { $taskUnit[$taskN - $taskOrder].ToString() }
    }
    $taskName = $taskCase.Name
    $taskLevel = $taskCase.Level
    $taskSource += "`n@[expose] def r_$taskName : Fin $taskLevel → ℤ := sparse![$taskLevel; $($taskEntries -join ', ')]`n"
    $taskSource += @"

eta_bench_begin
theorem bench_$taskName : first_coeffs $taskCountTerm (etaQuotient $taskLevel r_$taskName) =
    [$($taskValues -join ', ')] := by $TacticName
eta_bench_end "$taskName-$Count"
#print axioms bench_$taskName
"@
}
$taskInput = Join-Path $taskOutput "Bench$Count.lean"
[IO.File]::WriteAllText($taskInput, $taskSource, $taskUtf8)
if ($PrepareOnly) { Write-Output $taskInput; exit 0 }

$taskToolchain = [IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim()
$taskToolchainDir = $taskToolchain.Replace('/', '--').Replace(':', '---')
$taskLean = Join-Path $env:USERPROFILE ".elan/toolchains/$taskToolchainDir/bin/lean.exe"
$taskPaths = @($taskOutput, (Join-Path $taskRoot '.lake/build/lib/lean'))
$taskPaths += Get-ChildItem (Join-Path $taskRoot '.lake/packages') -Directory |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' }
$env:LEAN_PATH = $taskPaths -join ';'
$env:LEAN_NUM_THREADS = '2'
if ($taskTimerChanged -or !(Test-Path -LiteralPath (Join-Path $taskOutput 'EtaBenchTimer.olean'))) {
    $ErrorActionPreference = 'Continue'
    & $taskLean "--root=$taskOutput" $taskTimerInput '-o' (Join-Path $taskOutput 'EtaBenchTimer.olean')
    $taskTimerExit = $LASTEXITCODE
    $ErrorActionPreference = 'Stop'
    if ($taskTimerExit -ne 0) { exit $taskTimerExit }
}
$taskResults = @()
for ($taskRepeat = 1; $taskRepeat -le $Repeats; $taskRepeat++) {
    $taskLog = Join-Path $taskOutput "$Label-$Count-run$taskRepeat.log"
    $taskTimer = [Diagnostics.Stopwatch]::StartNew()
    $ErrorActionPreference = 'Continue'
    & $taskLean "--root=$taskOutput" $taskInput *> $taskLog
    $taskExit = $LASTEXITCODE
    $ErrorActionPreference = 'Stop'
    $taskTimer.Stop()
    $taskMetrics = @{}
    foreach ($taskLine in Get-Content -Encoding utf8 $taskLog) {
        if ($taskLine -match 'ETA_BENCH (\S+) (\d+)') {
            $taskMetrics[$Matches[1]] = [double]$Matches[2] / 1e9
        }
    }
    $taskResult = [ordered]@{ Label=$Label; Count=$Count; Repeat=$taskRepeat; ExitCode=$taskExit;
        ProcessSeconds=$taskTimer.Elapsed.TotalSeconds; Declarations=$taskMetrics }
    $taskResults += $taskResult
    $taskResult | ConvertTo-Json -Depth 5
    if ($taskExit -ne 0) { Get-Content -Encoding utf8 $taskLog -Tail 35; break }
}
[IO.File]::WriteAllText((Join-Path $taskOutput "$Label-$Count.json"),
    (ConvertTo-Json -Depth 8 -InputObject $taskResults), $taskUtf8)
exit $taskExit
