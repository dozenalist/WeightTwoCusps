param(
    [string]$Label = 'level462',
    [int]$Count = 100,
    [string]$Indices = '',
    [string]$TacticModule = 'WeightTwoCusps.Tactic.EtaCoefficient',
    [string]$TacticName = 'eta_coeff',
    [switch]$AsyncThroughput,
    [switch]$SerialThroughput,
    [switch]$PrepareOnly
)
$ErrorActionPreference = 'Stop'
if ($AsyncThroughput -and $SerialThroughput) { throw 'Choose one throughput mode.' }
$taskThroughput = $AsyncThroughput -or $SerialThroughput
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
$taskOutput = Join-Path $taskRoot '.lake/eta-opt'
[IO.Directory]::CreateDirectory($taskOutput) | Out-Null
$taskUtf8 = New-Object Text.UTF8Encoding($false)
$taskCases = Get-Content -Raw -Encoding utf8 'benchmarks/eta-coeff/level462-cases.json' | ConvertFrom-Json
$taskImports = Get-Content -Encoding utf8 'WeightTwoCusps/Levels/HasEtaQuotientBasis/462/Coefficients.lean' |
    Where-Object { $_ -match '^public import ' }
$taskSource = "module`n$($taskImports -join "`n")`npublic meta import EtaBenchTimer`npublic import $TacticModule`n"
$taskSource += @'
set_option Elab.async false
set_option maxRecDepth 4096
open WeightTwoCusps UpperHalfPlane
public section
'@
if ($TacticModule -eq 'EtaBaselineTactic') {
    # Keep fallback simplification on the isolated original procedures too.
    $taskProduction = [IO.File]::ReadAllText((Join-Path $taskRoot 'WeightTwoCusps/Tactic/EtaCoefficient.lean'))
    foreach ($taskMatch in [regex]::Matches($taskProduction,
        '(?m)^simproc(?:\s+[^\w\s]+)?\s+([A-Za-z][A-Za-z0-9_]*)\s+\(')) {
        $taskSource += "`nattribute [-simprocAttr] WeightTwoCusps.Tactic.$($taskMatch.Groups[1].Value)`n"
    }
}
$taskSelected = @($Indices.Split(',') | Where-Object { $_ -ne '' } | ForEach-Object { [int]$_ })
$taskStatements = 0
for ($taskIndex = 0; $taskIndex -lt $taskCases.Count; $taskIndex++) {
    if ($taskSelected.Count -gt 0 -and $taskIndex -notin $taskSelected) { continue }
    $taskCase = $taskCases[$taskIndex]
    $taskStatements++
    $taskUnit = New-Object 'System.Numerics.BigInteger[]' $Count
    $taskUnit[0] = 1
    $taskSum = 0
    foreach ($taskFactor in $taskCase.factors) {
        $taskM = [int]$taskFactor[0]
        $taskExponent = [int]$taskFactor[1]
        $taskSum += $taskM * $taskExponent
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
    $taskDilation = [int]$taskCase.dilation
    $taskValues = for ($taskN = 0; $taskN -lt $Count; $taskN++) {
        $taskDegree = [int][Math]::Floor($taskN / $taskDilation)
        if ($taskN % $taskDilation -ne 0 -or $taskDegree -lt $taskOrder) { '0' }
        else { $taskUnit[$taskDegree - $taskOrder].ToString() }
    }
    $taskSource += @"

eta_bench_begin
theorem bench_level462_$taskIndex : first_coeffs $Count $($taskCase.form) =
    [$($taskValues -join ', ')] := by $TacticName
eta_bench_end "level462-$taskIndex-$Count"
#print axioms bench_level462_$taskIndex
"@
}
if ($taskThroughput) {
    if ($AsyncThroughput) {
        $taskSource = $taskSource.Replace('set_option Elab.async false', 'set_option Elab.async true')
    }
    $taskSource = [regex]::Replace($taskSource,
        '(?m)^(public meta import EtaBenchTimer|eta_bench_begin|eta_bench_end[^\r\n]*|#print axioms[^\r\n]*)\r?\n?', '')
}
$taskModule = if ($SerialThroughput) { "Level462ThroughputSerial$Count" }
    elseif ($AsyncThroughput) { "Level462Throughput$Count" } else { "Level462Bench$Count" }
$taskInput = Join-Path $taskOutput "$taskModule.lean"
[IO.File]::WriteAllText($taskInput, $taskSource, $taskUtf8)
if ($PrepareOnly) { Write-Output $taskInput; exit 0 }
if (!$taskThroughput -and !(Test-Path -LiteralPath (Join-Path $taskOutput 'EtaBenchTimer.olean'))) {
    throw 'Run BenchmarkEtaCertification.ps1 once to initialize the imported timer.'
}
$taskToolchain = [IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim()
$taskToolchainDir = $taskToolchain.Replace('/', '--').Replace(':', '---')
$taskLean = Join-Path $env:USERPROFILE ".elan/toolchains/$taskToolchainDir/bin/lean.exe"
$taskPaths = @($taskOutput, (Join-Path $taskRoot '.lake/build/lib/lean'))
$taskPaths += Get-ChildItem (Join-Path $taskRoot '.lake/packages') -Directory |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' }
$env:LEAN_PATH = $taskPaths -join ';'
$env:LEAN_NUM_THREADS = '2'
$taskLog = Join-Path $taskOutput "$Label-$Count.log"
$taskTimer = [Diagnostics.Stopwatch]::StartNew()
$taskArguments = @("--root=$taskOutput", $taskInput)
if ($taskThroughput) { $taskArguments += @('-o', (Join-Path $taskOutput "$taskModule.olean")) }
$ErrorActionPreference = 'Continue'
& $taskLean @taskArguments *> $taskLog
$taskExit = $LASTEXITCODE
$ErrorActionPreference = 'Stop'
$taskTimer.Stop()
$taskMetrics = @{}
foreach ($taskLine in Get-Content -Encoding utf8 $taskLog) {
    if ($taskLine -match 'ETA_BENCH (\S+) (\d+)') {
        $taskMetrics[$Matches[1]] = [double]$Matches[2] / 1e9
    }
}
$taskMode = if ($SerialThroughput) { 'serial-compile' }
    elseif ($AsyncThroughput) { 'default-async-compile' } else { 'serial' }
$taskResult = [ordered]@{ Label=$Label; Count=$Count; Mode=$taskMode; Statements=$taskStatements; ExitCode=$taskExit;
    ProcessSeconds=$taskTimer.Elapsed.TotalSeconds; Declarations=$taskMetrics }
$taskJson = $taskResult | ConvertTo-Json -Depth 6
[IO.File]::WriteAllText((Join-Path $taskOutput "$Label-$Count.json"), $taskJson, $taskUtf8)
[pscustomobject]@{ Label=$Label; Count=$Count; Mode=$taskMode; ExitCode=$taskExit; Cases=$taskStatements;
    DeclarationSeconds=($taskMetrics.Values | Measure-Object -Sum).Sum;
    SlowestDeclarationSeconds=($taskMetrics.Values | Measure-Object -Maximum).Maximum;
    ProcessSeconds=$taskTimer.Elapsed.TotalSeconds } | ConvertTo-Json
Get-Content -Encoding utf8 $taskLog -Tail 12
exit $taskExit
