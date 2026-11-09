param(
    [ValidateSet('instrumentation', 'tau', 'level462', 'baseline')]
    [string]$Phase = 'instrumentation',
    [int]$Threads = 2
)

$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
$taskToolchain = [IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim()
$taskToolchainDir = $taskToolchain.Replace('/', '--').Replace(':', '---')
$taskLean = Join-Path $env:USERPROFILE ".elan/toolchains/$taskToolchainDir/bin/lean.exe"
$taskOutput = Join-Path $taskRoot '.lake/eta-profile'
$taskPaths = @($taskOutput, (Join-Path $taskRoot '.lake/build/lib/lean'))
$taskPaths += Get-ChildItem (Join-Path $taskRoot '.lake/packages') -Directory |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' }
$env:LEAN_PATH = $taskPaths -join ';'
$env:LEAN_NUM_THREADS = [string]$Threads

$taskModule = switch ($Phase) {
    'instrumentation' { 'EtaCoefficientProfile' }
    'tau' { 'TauProfile' }
    'level462' { 'Level462Profile' }
    'baseline' { 'TauBaseline' }
}
$taskInput = Join-Path $taskOutput "$taskModule.lean"
$taskLog = Join-Path $taskOutput "$taskModule.log"
$taskArguments = @("--root=$taskOutput", $taskInput)
if ($Phase -eq 'instrumentation') {
    $taskArguments += @('-o', (Join-Path $taskOutput "$taskModule.olean"))
}
$taskTimer = [Diagnostics.Stopwatch]::StartNew()
& $taskLean @taskArguments *> $taskLog
$taskExit = $LASTEXITCODE
$taskSummary = [pscustomobject]@{
    Phase = $Phase
    ExitCode = $taskExit
    ProcessSeconds = $taskTimer.Elapsed.TotalSeconds
    Threads = $Threads
}
$taskSummary | ConvertTo-Json | Set-Content -Encoding UTF8 (Join-Path $taskOutput "$taskModule-process.json")
Get-Content -Encoding UTF8 $taskLog -Tail 15
$taskSummary
exit $taskExit
