# Pi Chudnovsky

Build from the repository root:

```powershell
clang++ -O3 -mavx2 -std=c++17 pi\pi_chudnovsky.cpp src\*.cpp -o pi\pi_chudnovsky.exe
```

Build with FFT rounding-safety counters:

```powershell
clang++ -O3 -mavx2 -std=c++17 -DCOUNT_FFTS=1 pi\pi_chudnovsky.cpp src\*.cpp -o pi\pi_chudnovsky.exe
```

Run:

```powershell
.\pi\pi_chudnovsky.exe 1000
```

The argument is the number of digits after the decimal point. Long results print
as `first10digits...last10digits` by default.

For full output:

```powershell
.\pi\pi_chudnovsky.exe 1000 --full
```

Write the full output to a file while keeping console output short:

```powershell
.\pi\pi_chudnovsky.exe 100000 --file pi100000.txt
```

For phase timing:

```powershell
.\pi\pi_chudnovsky.exe 100000 --phases
```

On Windows, `cpu_time` uses `GetProcessTimes` to sum kernel and user CPU
time across process threads. Older builds used the Windows CRT `clock()`,
which measures elapsed time; their `cpu_time` cannot establish whether a run
was single-threaded. CPU time can exceed elapsed `time` in a parallel run.

`--bs-threads N` controls binary-splitting workers. `--threads 1` disables
internal VST/NTT transform parallelism, including inside those workers;
`--threads 0` selects the NTT pool's automatic thread count. Decimal conversion
has a separate parallel path. For a fully serial benchmark, also build with
`-DBC_CONVERT_PARALLEL_DEPTH=0` and use `--bs-threads 1 --threads 1`.

Build with `-DPI_TRACE_T_SHAPES=1` to log the actual limb pairs for both T
products at levels 0 through 4. Keep tracing disabled for performance comparisons.

Factor cancellation starts at level 4 (the root is level 0), reducing operands
before the larger upper-tree products. Build with
`-DPI_FACTOR_CANCEL_MIN_LEVEL=5` to compare against the previous threshold.

For an opt-in parallel throughput build, add `-DPI_OVERLAP_BS_SQRT=1`.
This overlaps binary splitting with square-root scaling, and can overlap the
final numerator with reciprocal calculation. It is disabled with `--threads 1`,
`--bs-threads 1`, or `--progress`. With `--phases`, `split_sqrt_wall` reports the
combined elapsed interval; `binary_split` and `sqrt_scale` overlap and must not
be added together. This can reduce elapsed time while increasing total CPU use.
