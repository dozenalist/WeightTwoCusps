$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
function Get-TaskMedian([double[]]$TaskValues) {
    $taskSorted = @($TaskValues | Sort-Object)
    $taskMiddle = [int][Math]::Floor($taskSorted.Count / 2)
    if ($taskSorted.Count % 2 -eq 1) { return $taskSorted[$taskMiddle] }
    return ($taskSorted[$taskMiddle - 1] + $taskSorted[$taskMiddle]) / 2
}
$taskRuns = @()
$taskThroughput = @()
$taskFailedRuns = @()
foreach ($taskFile in Get-ChildItem '.lake/eta-opt' -Filter '*.json') {
    foreach ($taskRecord in @(Get-Content -Raw -Encoding utf8 $taskFile.FullName | ConvertFrom-Json)) {
        if ($null -eq $taskRecord.Label) { continue }
        if ($taskRecord.ExitCode -ne 0) {
            $taskFailedRuns += $taskRecord
            continue
        }
        if ($taskRecord.ExitCode -eq 0 -and
            $taskRecord.Mode -in @('default-async-compile', 'serial-compile')) {
            $taskThroughput += $taskRecord
            continue
        }
        if ($null -ne $taskRecord.Label -and $null -ne $taskRecord.Declarations -and
            $taskRecord.ExitCode -eq 0 -and @($taskRecord.Declarations.PSObject.Properties).Count -gt 0) {
            $taskRuns += $taskRecord
        }
    }
}
$taskSummaries = @()
foreach ($taskGroup in $taskRuns | Group-Object Label,Count) {
    $taskRows = @($taskGroup.Group)
    $taskNames = @($taskRows | ForEach-Object { $_.Declarations.PSObject.Properties.Name } |
        Sort-Object -Unique)
    $taskMedians = [ordered]@{}
    foreach ($taskName in $taskNames) {
        $taskTimes = @($taskRows | ForEach-Object {
            $taskProperty = $_.Declarations.PSObject.Properties[$taskName]
            if ($null -ne $taskProperty) { [double]$taskProperty.Value }
        })
        $taskMedians[$taskName] = Get-TaskMedian $taskTimes
    }
    $taskSummary = [ordered]@{ Label=$taskRows[0].Label; Count=$taskRows[0].Count;
        Runs=$taskRows.Count; Cases=$taskNames.Count;
        SumOfCaseMedians=($taskMedians.Values | Measure-Object -Sum).Sum;
        MaximumCaseMedian=($taskMedians.Values | Measure-Object -Maximum).Maximum;
        MedianProcessSeconds=(Get-TaskMedian @($taskRows | ForEach-Object { $_.ProcessSeconds }));
        CaseMedians=$taskMedians }
    $taskSummaries += $taskSummary
    [pscustomobject]$taskSummary | Select-Object Label,Count,Runs,Cases,SumOfCaseMedians,
        MaximumCaseMedian,MedianProcessSeconds | Format-List
}
$taskHashes = [ordered]@{}
foreach ($taskSource in @('WeightTwoCusps/Tactic/EtaCoefficient.lean',
    'WeightTwoCusps/EtaQuotient/QExpansion/Certificates.lean',
    'WeightTwoCusps/EtaQuotient/QExpansion/PackedCertificates.lean',
    'WeightTwoCusps/Oldforms/QExpansion.lean',
    'WeightTwoCusps/Tactic/FirstCoeffsTests.lean')) {
    $taskHashes[$taskSource] = (Get-FileHash -Algorithm SHA256 -LiteralPath $taskSource).Hash
}
$taskValidation = [ordered]@{}
foreach ($taskEntry in @(
    @{ Name='CoefficientAndTacticBuild'; File='final-coefficients-build.json' },
    @{ Name='BasisIntegration'; File='final-lake-build-corrected.json' },
    @{ Name='AxiomAudit'; File='final-axiom-audit.json' },
    @{ Name='ResultConsistency'; File='final-result-consistency.json' }
)) {
    $taskPath = Join-Path $taskRoot ".lake/eta-opt/$($taskEntry.File)"
    if (Test-Path -LiteralPath $taskPath) {
        $taskValidation[$taskEntry.Name] = Get-Content -Raw -Encoding utf8 $taskPath | ConvertFrom-Json
    }
}
$taskResult = [ordered]@{ Toolchain=[IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim();
    Protocol='Native Windows; two Lean threads; synchronous declarations; default heartbeats; maxRecDepth 4096.';
    SourceSha256=$taskHashes; Summaries=$taskSummaries; Runs=$taskRuns;
    ThroughputRuns=$taskThroughput; FailedRuns=$taskFailedRuns; Validation=$taskValidation }
[IO.File]::WriteAllText((Join-Path $taskRoot 'benchmarks/eta-coeff/optimization-results.json'),
    (ConvertTo-Json -InputObject $taskResult -Depth 14), (New-Object Text.UTF8Encoding($false)))
