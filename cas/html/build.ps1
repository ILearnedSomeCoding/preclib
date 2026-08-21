param(
    [string]$Emsdk = $env:EMSDK
)

$ErrorActionPreference = 'Stop'
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$root = Resolve-Path (Join-Path $here '..\..')

$candidates = @()
if($Emsdk){
    if(Test-Path -LiteralPath $Emsdk -PathType Leaf){
        $candidates += $Emsdk
    }else{
        $candidates += (Join-Path $Emsdk 'upstream\emscripten\em++.exe')
        $candidates += (Join-Path $Emsdk 'upstream\emscripten\em++.bat')
        $candidates += (Join-Path $Emsdk 'em++.bat')
    }
}
$candidates += 'C:\emsdk\upstream\emscripten\em++.exe'
$candidates += 'C:\emsdk\upstream\emscripten\em++.bat'
$candidates += (Join-Path $env:USERPROFILE 'emsdk\upstream\emscripten\em++.exe')
$candidates += (Join-Path $env:USERPROFILE 'emsdk\upstream\emscripten\em++.bat')
$candidates += (Join-Path $env:USERPROFILE 'scoop\apps\emscripten\current\em++.bat')
$candidates += 'C:\ProgramData\chocolatey\bin\em++.bat'
$candidates += 'C:\ProgramData\anaconda3\Scripts\em++.bat'
$empp = $candidates | Where-Object { Test-Path -LiteralPath $_ } |
    Select-Object -First 1
if(-not $empp){
    $command = Get-Command 'em++' -ErrorAction SilentlyContinue
    if($command){ $empp = $command.Source }
}
if(-not $empp){
    throw 'em++ was not found. Run emsdk_env.bat or pass -Emsdk C:\path\to\emsdk.'
}

$sources = @(
    (Join-Path $here 'calculator_web.cpp')
)
$sources += Get-ChildItem (Join-Path $root 'cas\src') -Filter '*.cpp' |
    ForEach-Object FullName
$sources += Get-ChildItem (Join-Path $root 'src') -Filter '*.cpp' |
    ForEach-Object FullName

$arguments = @(
    # The CAS is small enough that code size matters more than peak Wasm
    # throughput in the browser. -Oz also improves the size of the embedded
    # base64 payload used by calculator_single.html.
    '-Oz', '-std=c++17', '-fexceptions',
    '-sMODULARIZE=1', '-sEXPORT_NAME=createCasModule',
    '-sENVIRONMENT=web,worker,node', '-sALLOW_MEMORY_GROWTH=1',
    '-sSINGLE_FILE=1',
    '-sINITIAL_MEMORY=67108864', '-sMAXIMUM_MEMORY=2147483648',
    '-sFILESYSTEM=0', '-sASSERTIONS=0',
    '-sEXPORTED_FUNCTIONS=["_cas_eval","_cas_set_precision","_cas_get_precision","_cas_node_count","_cas_collect","_cas_reset"]',
    '-sEXPORTED_RUNTIME_METHODS=["cwrap"]'
)
$arguments += $sources
$arguments += @('-o', (Join-Path $here 'cas_engine.js'))

& $empp @arguments
if($LASTEXITCODE -ne 0){ throw "Emscripten failed with exit code $LASTEXITCODE" }

# file:// pages cannot let a Worker import another local script. Package the
# engine and worker bootstrap as a Blob source that index.html can load.
$engineSource = [IO.File]::ReadAllText((Join-Path $here 'cas_engine.js'))
$workerSource = [IO.File]::ReadAllText((Join-Path $here 'worker.js'))
$workerSource = [Text.RegularExpressions.Regex]::Replace(
    $workerSource, '^importScripts\([^\r\n]*\);\r?\n', '')
$bundleSource = $engineSource + "`n" + $workerSource
$bundleJson = ConvertTo-Json $bundleSource -Compress
$utf8 = [Text.UTF8Encoding]::new($false)
[IO.File]::WriteAllText((Join-Path $here 'worker_bundle.js'),
    "window.CAS_WORKER_SOURCE=$bundleJson;", $utf8)

# Produce a genuinely standalone page. The Wasm is already embedded in
# cas_engine.js; worker_bundle.js then embeds that engine into a Blob Worker.
$html = [IO.File]::ReadAllText((Join-Path $here 'index.html'))
$css = [IO.File]::ReadAllText((Join-Path $here 'styles.css'))
$workerBase64 = [Convert]::ToBase64String($utf8.GetBytes($bundleSource))
$workerBundle = "window.CAS_WORKER_BASE64=`"$workerBase64`";"
$app = [IO.File]::ReadAllText((Join-Path $here 'app.js'))
$workerBundle = $workerBundle.Replace('</script>', '<\/script>')
$app = $app.Replace('</script>', '<\/script>')
$html = [Text.RegularExpressions.Regex]::Replace(
    $html, '<link rel="stylesheet" href="styles\.css">',
    [Text.RegularExpressions.MatchEvaluator]{
        param($match)
        "<style>`n$css`n</style>"
    })
$html = [Text.RegularExpressions.Regex]::Replace(
    $html, '<script src="worker_bundle\.js[^\"]*"></script>',
    [Text.RegularExpressions.MatchEvaluator]{
        param($match)
        "<script>`n$workerBundle`n</script>"
    })
$html = [Text.RegularExpressions.Regex]::Replace(
    $html, '<script src="app\.js[^\"]*"></script>',
    [Text.RegularExpressions.MatchEvaluator]{
        param($match)
        "<script>`n$app`n</script>"
    })
[IO.File]::WriteAllText((Join-Path $here 'calculator_single.html'), $html, $utf8)

function Write-GzipFile([string]$path){
    $input = [IO.File]::OpenRead($path)
    try{
        $output = [IO.File]::Create("$path.gz")
        try{
            $gzip = [IO.Compression.GZipStream]::new(
                $output, [IO.Compression.CompressionLevel]::Optimal)
            try{ $input.CopyTo($gzip) }
            finally{ $gzip.Dispose() }
        }finally{ $output.Dispose() }
    }finally{ $input.Dispose() }
}

$artifacts = @(
    (Join-Path $here 'cas_engine.js'),
    (Join-Path $here 'worker_bundle.js'),
    (Join-Path $here 'calculator_single.html')
)
foreach($artifact in $artifacts){
    Write-GzipFile $artifact
    $brotli = Get-Command 'brotli' -ErrorAction SilentlyContinue
    if($brotli){ & $brotli.Source '-f' '-q' '11' $artifact }
}

Write-Host "Built CAS assets plus .gz and .br compressed variants"
