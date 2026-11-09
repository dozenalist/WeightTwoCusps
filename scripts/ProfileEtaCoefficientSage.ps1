param(
    [ValidateSet('TauProfile', 'Level462Profile')]
    [string]$Workload = 'TauProfile',
    [int]$Launches = 3
)

$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
$taskDirectory = Join-Path $taskRoot '.lake/eta-profile'
$taskRequestPath = Join-Path $taskDirectory "$Workload-sage-input.json"
$taskRequestData = [IO.File]::ReadAllText($taskRequestPath) | ConvertFrom-Json
$taskAdapter = Join-Path (Split-Path -Parent $taskRoot) 'Determinant/scripts/Invoke-SageWSL.ps1'
function Invoke-EtaSageBenchmark([string]$Suffix, [int]$Rounds) {
    $taskRequestData | Add-Member -MemberType NoteProperty -Name rounds -Value $Rounds -Force
    $taskRequest = $taskRequestData | ConvertTo-Json -Depth 10 -Compress
    $taskOutput = Join-Path $taskDirectory "$Workload-sage-$Suffix.json"
    $taskTimer = [Diagnostics.Stopwatch]::StartNew()
    $taskRequest | & powershell -NoProfile -ExecutionPolicy Bypass -File $taskAdapter `
        -Script 'scripts/benchmark_eta_coeff_sage.py' *> $taskOutput
    $taskExit = $LASTEXITCODE
    $taskSeconds = $taskTimer.Elapsed.TotalSeconds
    if ($taskExit -ne 0) {
        Get-Content -Encoding UTF8 $taskOutput
        throw "Sage workload failed with exit code $taskExit"
    }
    $taskResponse = [IO.File]::ReadAllText($taskOutput) | ConvertFrom-Json
    if ($taskResponse.status -ne 'ok') { throw 'Sage validation failed.' }
    return [pscustomobject]@{
        Launch = $Suffix
        WallSeconds = $taskSeconds
        SageVersion = $taskResponse.sage_version
        Jobs = $taskResponse.jobs
        InputParseNs = $taskResponse.input_parse_ns
        SageImportNs = $taskResponse.sage_import_ns
        Rounds = $taskResponse.rounds
        InitialJsonEncodeNs = $taskResponse.initial_json_encode_ns
        InitialJsonBytes = $taskResponse.initial_json_bytes
        InputBytes = [Text.Encoding]::UTF8.GetByteCount($taskRequest)
        OutputBytes = [Text.Encoding]::UTF8.GetByteCount(([IO.File]::ReadAllText($taskOutput)).Trim())
    }
}
$taskResults = @()
for ($taskIteration = 1; $taskIteration -le $Launches; $taskIteration++) {
    $taskResult = Invoke-EtaSageBenchmark ([string]$taskIteration) 1
    $taskResults += $taskResult
    Write-Output "Sage $Workload launch $taskIteration`: $($taskResult.WallSeconds) seconds; $($taskResult.Jobs) jobs validated."
}
$taskWarm = Invoke-EtaSageBenchmark 'warm' 5
[pscustomobject]@{ Fresh = $taskResults; Warm = $taskWarm } |
    ConvertTo-Json -Depth 6 | Set-Content -Encoding UTF8 `
    (Join-Path $taskDirectory "$Workload-sage-summary.json")
