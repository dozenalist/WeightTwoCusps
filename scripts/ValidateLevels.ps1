param([int]$Threads = 4)

$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
if (-not $env:ELAN_HOME) {
    $env:ELAN_HOME = Join-Path ([Environment]::GetFolderPath('UserProfile')) '.elan'
}
$env:LEAN_NUM_THREADS = [string]$Threads
$taskTimer = [Diagnostics.Stopwatch]::StartNew()
$taskTargets = @(
    'WeightTwoCusps',
    'WeightTwoCusps.Tactic.BasicTests',
    'WeightTwoCusps.Tactic.EtaCoefficientTests',
    'WeightTwoCusps.Tactic.EtaCoefficientBenchmarks',
    'WeightTwoCusps.Tactic.FirstCoeffsTests',
    'WeightTwoCusps.Tactic.EtaOldformTests',
    'WeightTwoCusps.Oldforms.Tests',
    'WeightTwoCusps.Basis.Tests',
    'WeightTwoCusps.Tactic.RescaleCoefficientTests',
    'WeightTwoCusps.Tactic.BasisDeterminantTests',
    'WeightTwoCusps.Levels.Tests'
)
$taskBuildLog = Join-Path $taskRoot '.lake/LevelValidationBuild.log'
& lake --log-level=error build @taskTargets *> $taskBuildLog
if ($LASTEXITCODE -ne 0) { throw "Library/regression build failed; see $taskBuildLog" }

$taskTable = [IO.File]::ReadAllText((Join-Path $taskRoot 'WeightTwoCusps/Levels/HasEtaQuotientBasis/TABLE.md'))
$taskRows = [regex]::Matches($taskTable,
    '(?m)^\| \[(\d+)\]\(#level-\d+\) \| \d+ \| (\d+) \| \d+ \| (YES|NO) \| \d+ \|')
if ($taskRows.Count -ne 500) { throw 'Expected exactly 500 level table rows.' }
$taskRootModule = [IO.File]::ReadAllText((Join-Path $taskRoot 'WeightTwoCusps.lean'))
$taskFullLevels = 0
foreach ($taskRow in $taskRows) {
    $taskN = $taskRow.Groups[1].Value
    if ($taskRow.Groups[2].Value -ne '0' -and $taskRow.Groups[3].Value -eq 'YES') {
        $taskFullLevels++
        $taskModule = "WeightTwoCusps.Levels.HasEtaQuotientBasis.«$taskN».Basis"
        if (-not $taskRootModule.Contains("public import $taskModule")) {
            throw "Missing full-basis export: $taskModule"
        }
    }
}

$taskNames = [Collections.Generic.HashSet[string]]::new()
$taskFormCount = 0
foreach ($taskFile in (Get-ChildItem -LiteralPath (Join-Path $taskRoot 'WeightTwoCusps/Levels') -Recurse -Filter '*.lean')) {
    $taskSource = [IO.File]::ReadAllText($taskFile.FullName)
    foreach ($taskMatch in [regex]::Matches($taskSource,
        '(?m)^(?:@\[[^\]]+\]\s+)?(?:abbrev|def|theorem)\s+((?:cuspForm_|level_)\w+)')) {
        $taskName = $taskMatch.Groups[1].Value
        $taskNamespace = if ($taskFile.Name -eq 'Tests.lean') { 'WeightTwoCusps.LevelRangeTests' } else { 'WeightTwoCusps' }
        [void]$taskNames.Add("$taskNamespace.$taskName")
    }
    if ($taskFile.Name -notin @('Basis.lean', 'Tests.lean', 'Coefficients.lean')) {
        $taskFormCount++
        $taskStem = [IO.Path]::GetFileNameWithoutExtension($taskFile.Name)
        if ($taskSource -notmatch ('(?m)^abbrev cuspForm_' + [regex]::Escape($taskStem) + '\s*:')) {
            throw "Filename/declaration mismatch: $($taskFile.FullName)"
        }
    }
}

$taskAuditPath = Join-Path $taskRoot '.lake/LevelValidationAxioms.lean'
$taskAuditLog = Join-Path $taskRoot '.lake/LevelValidationAxioms.log'
$taskAudit = [Text.StringBuilder]::new()
[void]$taskAudit.AppendLine('import WeightTwoCusps.Levels.Tests')
[void]$taskAudit.AppendLine('set_option maxRecDepth 16384')
foreach ($taskName in ($taskNames | Sort-Object)) { [void]$taskAudit.AppendLine("#print axioms $taskName") }
[IO.File]::WriteAllText($taskAuditPath, $taskAudit.ToString())
& lake env lean $taskAuditPath *> $taskAuditLog
if ($LASTEXITCODE -ne 0) { throw "Axiom audit failed; see $taskAuditLog" }
$taskAxioms = [regex]::Matches([IO.File]::ReadAllText($taskAuditLog), 'depends on axioms:\s*\[([^\]]*)\]')
$taskNoAxioms = [regex]::Matches([IO.File]::ReadAllText($taskAuditLog), 'does not depend on any axioms')
if ($taskAxioms.Count + $taskNoAxioms.Count -ne $taskNames.Count) { throw 'The axiom audit did not cover every declaration.' }
foreach ($taskMatch in $taskAxioms) {
    foreach ($taskAxiom in ($taskMatch.Groups[1].Value -split ',')) {
        if ($taskAxiom.Trim() -notin @('propext', 'Classical.choice', 'Quot.sound')) {
            throw "Unexpected axiom: $taskAxiom"
        }
    }
}
$taskSummary = [pscustomobject]@{
    Levels = $taskRows.Count
    FullPositiveDimensionalEtaBases = $taskFullLevels
    FormModules = $taskFormCount
    AuditedDeclarations = $taskNames.Count
    UnexpectedAxioms = @()
    HeartbeatOverride = $false
    Seconds = $taskTimer.Elapsed.TotalSeconds
    Targets = $taskTargets
}
$taskSummary | ConvertTo-Json -Depth 3 | Set-Content -Encoding UTF8 (Join-Path $taskRoot '.lake/LevelValidation.json')
$taskSummary
