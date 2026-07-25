#!/usr/bin/env python3
"""Parameter sweep for the exact Wall-I research laboratory.

This script does not promote finite-cutoff observations to PDE theorems. It
searches the proof-design space and records where a proposed lane succeeds or
fails under the frozen finite model.
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import List

import ns_periodic_wall_i_lab as lab


def parse_int_list(text: str) -> List[int]:
    values = [int(part.strip()) for part in text.split(",") if part.strip()]
    if not values:
        raise argparse.ArgumentTypeError(
            "expected a nonempty comma-separated integer list"
        )
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoffs", type=parse_int_list, default=[2, 3, 4])
    parser.add_argument("--output-shells", type=parse_int_list, default=[1, 2])
    parser.add_argument("--separations", type=parse_int_list, default=[2, 3, 4, 8])
    parser.add_argument("--weight-exponents", type=parse_int_list, default=[0, 1, 2])
    parser.add_argument("--sobolev-twice", type=parse_int_list, default=[6, 7, 8, 9])
    parser.add_argument("--overlap", type=int, default=1)
    parser.add_argument("--max-schur-entries", type=int, default=2_000_000)
    parser.add_argument(
        "--out-prefix", type=Path, default=Path("wall_i_sweep")
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    rows = []
    for cutoff in args.cutoffs:
        for shell in args.output_shells:
            if shell > lab.dyadic_level_from_radius(max(1, cutoff)) + 1:
                continue
            triad = lab.triad_geometry_report(
                cutoff, shell, min(args.separations), args.overlap
            )
            for separation in args.separations:
                for exponent in args.weight_exponents:
                    schur = lab.far_low_schur_report(
                        cutoff,
                        shell,
                        separation,
                        args.overlap,
                        exponent,
                        args.max_schur_entries,
                    )
                    rows.append({
                        "lane": "far-low",
                        "cutoff": cutoff,
                        "output_shell": shell,
                        "separation": separation,
                        "weight_exponent": exponent,
                        "triad_count": triad.triad_count,
                        "row_max": schur.row_max,
                        "column_max": schur.column_max,
                        "schur_product": schur.product,
                        "schur_product_float": schur.product_float,
                        "exact_complete": schur.exact_complete,
                    })
    for separation in args.separations:
        for s2 in args.sobolev_twice:
            high = lab.far_high_tail_report(separation, s2)
            rows.append({
                "lane": "far-high",
                "cutoff": "",
                "output_shell": "",
                "separation": separation,
                "weight_exponent": "",
                "sobolev_twice": s2,
                "tail": high.get("two_placements"),
                "fits_one_sixteenth": high.get("fits_one_sixteenth"),
                "fits_one_eighth": high.get("fits_one_eighth"),
                "exact_complete": high.get("exact_rational", False),
            })

    prefix = args.out_prefix
    prefix.parent.mkdir(parents=True, exist_ok=True)
    csv_path = prefix.with_suffix(".csv")
    json_path = prefix.with_suffix(".json")
    fieldnames = sorted({key for row in rows for key in row})
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    json_path.write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    complete_far_low = [
        row for row in rows
        if row["lane"] == "far-low" and row.get("exact_complete")
    ]
    best = (
        min(complete_far_low, key=lambda row: row["schur_product_float"])
        if complete_far_low else None
    )
    print(json.dumps({
        "status": "finite-reconnaissance-not-proof",
        "rows": len(rows),
        "best_finite_far_low": best,
        "csv": str(csv_path),
        "json": str(json_path),
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
