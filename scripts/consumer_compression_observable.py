#!/usr/bin/env python3
"""Compute C_t(Q): minimum carrier cost among adequate carriers at each checkpoint.

Input CSV columns:
  time,carrier,cost,adequate

`adequate` accepts true/false, 1/0, yes/no.

The script deliberately reports only a consumer-relative compression observable.
A decline in C_t(Q) is not labelled as grokking, Kolmogorov compression, causal
identification, or mechanistic explanation.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from collections import defaultdict
from pathlib import Path

TRUE = {"1", "true", "yes", "y"}
FALSE = {"0", "false", "no", "n"}


def parse_bool(raw: str) -> bool:
    value = raw.strip().lower()
    if value in TRUE:
        return True
    if value in FALSE:
        return False
    raise ValueError(f"invalid adequate value: {raw!r}")


def load_rows(path: Path) -> list[dict[str, object]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        required = {"time", "carrier", "cost", "adequate"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise ValueError(f"missing required columns: {sorted(missing)}")
        rows: list[dict[str, object]] = []
        for line_no, row in enumerate(reader, start=2):
            try:
                cost = int(row["cost"])
                adequate = parse_bool(row["adequate"])
            except Exception as exc:
                raise ValueError(f"line {line_no}: {exc}") from exc
            if cost < 0:
                raise ValueError(f"line {line_no}: cost must be non-negative")
            rows.append(
                {
                    "time": row["time"].strip(),
                    "carrier": row["carrier"].strip(),
                    "cost": cost,
                    "adequate": adequate,
                }
            )
    return rows


def compute_ctq(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    order: list[str] = []
    for row in rows:
        time = str(row["time"])
        if time not in grouped:
            order.append(time)
        grouped[time].append(row)

    result: list[dict[str, object]] = []
    for time in order:
        adequate = [row for row in grouped[time] if bool(row["adequate"])]
        if not adequate:
            result.append(
                {
                    "time": time,
                    "ctq": None,
                    "selected_carriers": [],
                    "status": "no adequate carrier",
                }
            )
            continue
        minimum = min(int(row["cost"]) for row in adequate)
        selected = sorted(
            str(row["carrier"])
            for row in adequate
            if int(row["cost"]) == minimum
        )
        result.append(
            {
                "time": time,
                "ctq": minimum,
                "selected_carriers": selected,
                "status": "minimum adequate carrier cost",
            }
        )
    return result


def self_test() -> None:
    rows = [
        {"time": "early", "carrier": "full", "cost": 3, "adequate": True},
        {"time": "early", "carrier": "mid", "cost": 2, "adequate": False},
        {"time": "early", "carrier": "compact", "cost": 1, "adequate": False},
        {"time": "transition", "carrier": "full", "cost": 3, "adequate": True},
        {"time": "transition", "carrier": "mid", "cost": 2, "adequate": True},
        {"time": "transition", "carrier": "compact", "cost": 1, "adequate": False},
        {"time": "late", "carrier": "full", "cost": 3, "adequate": True},
        {"time": "late", "carrier": "mid", "cost": 2, "adequate": True},
        {"time": "late", "carrier": "compact", "cost": 1, "adequate": True},
    ]
    result = compute_ctq(rows)
    assert [row["ctq"] for row in result] == [3, 2, 1]
    print(json.dumps({"self_test": "ok", "ctq": result}, indent=2))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", nargs="?", type=Path)
    parser.add_argument("--json", action="store_true", help="emit JSON instead of CSV")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return 0
    if args.csv is None:
        parser.error("CSV path is required unless --self-test is used")

    try:
        result = compute_ctq(load_rows(args.csv))
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps({"observable": "C_t(Q)", "rows": result}, indent=2))
    else:
        writer = csv.DictWriter(
            sys.stdout,
            fieldnames=["time", "ctq", "selected_carriers", "status"],
        )
        writer.writeheader()
        for row in result:
            row = dict(row)
            row["selected_carriers"] = ";".join(row["selected_carriers"])
            writer.writerow(row)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
