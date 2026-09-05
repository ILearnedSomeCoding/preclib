import argparse
import csv
from collections import defaultdict

import matplotlib.pyplot as plt


def load_rows(path):
    with open(path, newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    for row in rows:
        for key in ("a_limbs", "b_limbs", "result_limbs", "reps", "samples"):
            row[key] = int(row[key])
        for key in ("prec_seconds", "gmp_seconds", "ratio"):
            row[key] = float(row[key])
    return rows


def draw_operation(rows, operation, timing_ax, ratio_ax):
    groups = defaultdict(list)
    for row in rows:
        if row["operation"] == operation:
            groups[row["shape"]].append(row)

    for shape, values in sorted(groups.items()):
        values.sort(key=lambda row: row["b_limbs"])
        x = [row["b_limbs"] for row in values]
        prec = [row["prec_seconds"] for row in values]
        gmp = [row["gmp_seconds"] for row in values]
        ratio = [row["ratio"] for row in values]
        line = timing_ax.plot(x, prec, marker="o", markersize=3,
                              linewidth=1.4, label=f"prec {shape}")[0]
        timing_ax.plot(x, gmp, linestyle="--", linewidth=1.2,
                       color=line.get_color(), label=f"GMP {shape}")
        ratio_ax.plot(x, ratio, marker="o", markersize=3,
                      linewidth=1.4, label=shape)

    timing_ax.set_xscale("log", base=2)
    timing_ax.set_yscale("log")
    timing_ax.set_title(f"{operation}: wall time per operation")
    timing_ax.set_ylabel("seconds")
    timing_ax.grid(True, which="both", alpha=0.25)
    timing_ax.legend(fontsize=8, ncol=2)

    ratio_ax.set_xscale("log", base=2)
    ratio_ax.set_yscale("log", base=2)
    ratio_ax.axhline(1.0, color="black", linewidth=1)
    ratio_ax.set_title(f"{operation}: prec / GMP (below 1 is faster)")
    ratio_ax.set_xlabel("divisor limbs" if operation == "div" else "smaller operand limbs")
    ratio_ax.set_ylabel("time ratio")
    ratio_ax.grid(True, which="both", alpha=0.25)
    ratio_ax.legend(fontsize=8, ncol=2)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", nargs="?", default="test/bench_gmp_full.csv")
    parser.add_argument("--output", default="test/bench_gmp_full.png")
    args = parser.parse_args()

    rows = load_rows(args.csv)
    fig, axes = plt.subplots(2, 2, figsize=(16, 10), constrained_layout=True)
    # Show squaring beside the multiplication shapes without duplicating it in
    # the benchmark CSV.
    square_rows = [dict(row, operation="mul", shape="square")
                   for row in rows if row["operation"] == "square"]
    draw_operation(rows + square_rows, "mul", axes[0, 0], axes[1, 0])
    draw_operation(rows, "div", axes[0, 1], axes[1, 1])
    fig.suptitle("prec-cpp vs GMP comprehensive benchmark", fontsize=16)
    fig.savefig(args.output, dpi=170)
    print(args.output)


if __name__ == "__main__":
    main()
