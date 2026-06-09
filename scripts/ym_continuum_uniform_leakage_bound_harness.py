#!/usr/bin/env python3
"""Diagnostic harness for the YM continuum uniform leakage bound."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class LeakageRow:
    p: int
    depth: int
    c_g: float
    leakage_bound: float
    decays_from_previous: bool


def build_rows(p: int, c_g: float, max_depth: int) -> list[LeakageRow]:
    rows: list[LeakageRow] = []
    prev = None
    for depth in range(1, max_depth + 1):
        leakage = c_g * (p ** (-depth))
        rows.append(
            LeakageRow(
                p=p,
                depth=depth,
                c_g=c_g,
                leakage_bound=leakage,
                decays_from_previous=(prev is None or leakage < prev),
            )
        )
        prev = leakage
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    parser.add_argument("--p", type=int, default=3)
    parser.add_argument("--cg", type=float, default=0.8)
    parser.add_argument("--depth", type=int, default=6)
    args = parser.parse_args()

    rows = build_rows(args.p, args.cg, args.depth)
    payload = {
        "contract": "YM continuum uniform leakage bound smoke",
        "diagnostic_only": True,
        "promotion": {"leakage_bound_proved": False, "ym_clay_promoted": False, "terminal_promoted": False},
        "summary": {
            "all_rows_decay": all(r.decays_from_previous for r in rows),
            "final_leakage_bound": rows[-1].leakage_bound,
            "formula": "L_d <= C_G * p^(-d)",
        },
        "rows": [asdict(r) for r in rows],
    }
    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"all_rows_decay={payload['summary']['all_rows_decay']}")
        print(f"final_leakage_bound={payload['summary']['final_leakage_bound']:.12f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
