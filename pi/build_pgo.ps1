param(
    [int]$TrainingDigits = 1000000,
    [int]$Threads = 2
)

$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$generated = Join-Path $PSScriptRoot 'pi_chudnovsky_pgo_gen.exe'
$raw = Join-Path $PSScriptRoot 'pi_chudnovsky.profraw'
$profile = Join-Path $PSScriptRoot 'pi_chudnovsky.profdata'
$output = Join-Path $PSScriptRoot 'pi_chudnovsky.exe'
$sources = Get-ChildItem (Join-Path $root 'src') -Filter '*.cpp' |
    ForEach-Object { $_.FullName }

Push-Location $root
try {
    & clang++ -O3 -mavx2 -std=c++17 -fprofile-instr-generate `
        (Join-Path $PSScriptRoot 'pi_chudnovsky.cpp') $sources -o $generated
    if($LASTEXITCODE -ne 0){ exit $LASTEXITCODE }

    $env:LLVM_PROFILE_FILE = $raw
    & $generated $TrainingDigits --threads $Threads
    if($LASTEXITCODE -ne 0){ exit $LASTEXITCODE }

    & llvm-profdata merge -o $profile $raw
    if($LASTEXITCODE -ne 0){ exit $LASTEXITCODE }

    & clang++ -O3 -mavx2 -std=c++17 "-fprofile-instr-use=$profile" `
        (Join-Path $PSScriptRoot 'pi_chudnovsky.cpp') $sources -o $output
    exit $LASTEXITCODE
} finally {
    Pop-Location
}
