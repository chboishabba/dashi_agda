#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


QT_EDGES = [
    0.0,
    0.3647504,
    0.7295008,
    1.0942512,
    1.4590016,
    1.823752,
    2.1885024,
    2.6444404,
    3.1003784,
    4.103442,
    5.1976932,
    6.5655072,
    8.2980716,
    10.395386,
    15.045954,
    23.526401,
    47.782302,
    105.1393,
    298.82177,
]


@dataclass(frozen=True)
class BinResult:
    index: int
    low: float
    high: float
    differential: float
    differential_uncertainty: float
    integrated: float
    integrated_uncertainty: float
    txt_path: str


def parse_bins(selection: str) -> list[int]:
    if selection == "all":
        return list(range(len(QT_EDGES) - 1))
    bins: set[int] = set()
    for part in selection.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            start_s, end_s = part.split("-", 1)
            start = int(start_s)
            end = int(end_s)
            bins.update(range(start, end + 1))
        else:
            bins.add(int(part))
    bad = sorted(index for index in bins if index < 0 or index >= len(QT_EDGES) - 1)
    if bad:
        raise SystemExit(f"bin indices out of range: {bad}")
    return sorted(bins)


def run_cmd(cmd: list[str], cwd: Path) -> None:
    print("+ " + " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def read_dyturbo_txt(path: Path) -> tuple[float, float, float, float]:
    rows = []
    for raw_line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        parts = raw_line.split()
        if len(parts) != 2:
            continue
        try:
            rows.append((float(parts[0]), float(parts[1])))
        except ValueError:
            continue
    if len(rows) < 2:
        raise ValueError(f"expected differential and integrated rows in {path}")
    return rows[0][0], rows[0][1], rows[1][0], rows[1][1]


def write_xs_qt_dat(path: Path, results: list[BinResult], use_integrated: bool) -> None:
    if not results:
        raise ValueError("no results to assemble")
    edges = [result.low for result in results] + [results[-1].high]
    pairs = []
    for result in results:
        if use_integrated:
            pairs.extend([result.integrated, result.integrated_uncertainty])
        else:
            pairs.extend([result.differential, result.differential_uncertainty])
    n_edges = len(edges)
    n_cells = n_edges + 1
    tokens = (
        ["h", "1", str(n_edges)]
        + [f"{edge:.10g}" for edge in edges]
        + ["0", "0", str(n_cells), "0", "0"]
        + [f"{value:.12g}" for value in pairs]
        + ["5", "x", "s", "_", "q", "t", "2", "q", "t"]
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(" ".join(tokens) + "\n", encoding="utf-8")


def run_channel(args: argparse.Namespace, channel: str, bins: list[int]) -> tuple[Path, list[BinResult]]:
    results: list[BinResult] = []
    for ordinal, index in enumerate(bins, start=1):
        low = QT_EDGES[index]
        high = QT_EDGES[index + 1]
        run_dir = Path(args.base_run_dir) / f"{channel}_bin_{index:02d}"
        output_dir = run_dir / "generated_cms_smp_20_003"
        suffix = f"{channel}_b{index:02d}_{args.calls}"
        print(
            json.dumps(
                {
                    "event": "bin_start",
                    "channel": channel,
                    "bin": index,
                    "ordinal": ordinal,
                    "total": len(bins),
                    "qT_low": low,
                    "qT_high": high,
                },
                sort_keys=True,
            ),
            flush=True,
        )
        generate_cmd = [
            sys.executable,
            "scripts/generate_dyturbo_cms_cards.py",
            "--cut-mode",
            "exact-cms-leading-subleading",
            "--calls",
            str(args.calls),
            "--qt-bins",
            f"{low} {high}",
            "--output-suffix",
            suffix,
            "--output-dir",
            str(output_dir),
            "--dyturbo-bin",
            str(args.dyturbo),
        ]
        if args.xqtcut is not None:
            generate_cmd += ["--xqtcut", str(args.xqtcut)]
        run_cmd(generate_cmd, Path.cwd())
        card = output_dir / f"t43_{channel}_fpc_exactcms_fixed.in"
        run_cmd(
            [
                sys.executable,
                "scripts/run_dyturbo_with_progress.py",
                str(card.relative_to(run_dir)),
                "--run-dir",
                str(run_dir),
                "--dyturbo",
                str(Path(args.dyturbo).resolve()),
                "--heartbeat-seconds",
                str(args.heartbeat_seconds),
                "--progress-jsonl",
                f"progress/t43_{channel}_bin_{index:02d}.jsonl",
            ]
            + (["--echo"] if args.echo else []),
            Path.cwd(),
        )
        txt_path = run_dir / f"dyturbo_t43_{channel}_fpc_exactcms_fixed_{suffix}.txt"
        differential, differential_unc, integrated, integrated_unc = read_dyturbo_txt(txt_path)
        result = BinResult(
            index=index,
            low=low,
            high=high,
            differential=differential,
            differential_uncertainty=differential_unc,
            integrated=integrated,
            integrated_uncertainty=integrated_unc,
            txt_path=str(txt_path),
        )
        print(
            json.dumps(
                {
                    "event": "bin_complete",
                    "channel": channel,
                    "bin": index,
                    "differential": differential,
                    "integrated": integrated,
                    "positive": differential > 0.0 and integrated > 0.0,
                },
                sort_keys=True,
            ),
            flush=True,
        )
        results.append(result)

    assembled = Path(args.output_dir) / f"dyturbo_t43_{channel}_per_bin_exactcms_{args.calls}.dat"
    write_xs_qt_dat(assembled, results, args.use_integrated)
    return assembled, results


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run exact-CMS DYTurbo t43 as independent one-bin jobs and assemble xs_qt grids."
    )
    parser.add_argument("--channels", default="num,den", help="Comma list: num, den, or num,den.")
    parser.add_argument("--bins", default="all", help="0-based bin list/ranges, e.g. all, 13, 0-13, 5,13.")
    parser.add_argument("--calls", type=int, default=2000)
    parser.add_argument("--base-run-dir", default="temp-DOWNLOADED/dyturbo/run_cms_per_bin")
    parser.add_argument("--output-dir", default="temp-DOWNLOADED/dyturbo/run_cms_per_bin/assembled")
    parser.add_argument("--dyturbo", default="temp-DOWNLOADED/dyturbo/patched/bin/dyturbo")
    parser.add_argument("--heartbeat-seconds", type=float, default=30.0)
    parser.add_argument("--xqtcut", help="Optional xqtcut override passed to generated cards.")
    parser.add_argument("--use-integrated", action="store_true")
    parser.add_argument("--echo", action="store_true")
    args = parser.parse_args()

    bins = parse_bins(args.bins)
    channels = [part.strip() for part in args.channels.split(",") if part.strip()]
    bad_channels = [channel for channel in channels if channel not in {"num", "den"}]
    if bad_channels:
        raise SystemExit(f"unknown channels: {bad_channels}")

    summary = {
        "calls": args.calls,
        "bins": bins,
        "channels": {},
        "use_integrated": args.use_integrated,
    }
    for channel in channels:
        assembled, results = run_channel(args, channel, bins)
        summary["channels"][channel] = {
            "assembled_dat": str(assembled),
            "results": [result.__dict__ for result in results],
        }

    summary_path = Path(args.output_dir) / f"dyturbo_t43_per_bin_exactcms_{args.calls}_summary.json"
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"event": "complete", "summary": str(summary_path)}, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
