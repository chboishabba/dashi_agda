#!/usr/bin/env python3
"""Verify a FLINT/Arb climbing-gym NDJSON certificate bundle exactly.

This checker performs no floating-point arithmetic.  Every Arb interval is read
as an exact dyadic interval [a,b] * 2**e and converted to Fraction endpoints.
For rows marked ``cell_unique`` it independently verifies that the *whole*
phase interval lies strictly inside the declared j / p**a cell.

Authority boundary
------------------
Passing this checker proves integrity/consistency of the emitted interval and
cell arithmetic.  It does not prove that the external interval really encloses
the n-th zeta zero, does not import FLINT correctness into Agda, and does not
establish Monster specificity or RH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

SCHEMA_VERSION = "1.0.0"


def dyadic_endpoint(mantissa: str | int, two_exp: str | int) -> Fraction:
    m = int(mantissa)
    e = int(two_exp)
    return Fraction(m << e, 1) if e >= 0 else Fraction(m, 1 << (-e))


def dyadic_interval(obj: dict[str, Any]) -> tuple[Fraction, Fraction]:
    e = obj["two_exp"]
    lo = dyadic_endpoint(obj["lower_mantissa"], e)
    hi = dyadic_endpoint(obj["upper_mantissa"], e)
    if lo > hi:
        raise ValueError("reversed dyadic interval")
    return lo, hi


def strict_cell_for_interval(
    lo: Fraction,
    hi: Fraction,
    *,
    wall_n: int,
    cell_index: int,
) -> bool:
    if wall_n <= 0 or not (0 <= cell_index < wall_n):
        return False
    return Fraction(cell_index, wall_n) < lo and hi < Fraction(cell_index + 1, wall_n)


def inferred_unique_cell(lo: Fraction, hi: Fraction, wall_n: int) -> int | None:
    """Return j iff the complete *closed* interval is strictly in one open cell."""
    if wall_n <= 0 or lo < 0 or hi > 1:
        return None
    # Candidate from lower endpoint; strict inequalities below reject boundaries.
    j = (lo.numerator * wall_n) // lo.denominator
    return j if strict_cell_for_interval(lo, hi, wall_n=wall_n, cell_index=j) else None


def load_ndjson(path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    lines = [line for line in path.read_text().splitlines() if line.strip()]
    if not lines:
        raise ValueError("empty certificate bundle")
    objects = [json.loads(line) for line in lines]
    metadata = objects[0]
    if metadata.get("type") != "metadata":
        raise ValueError("first row must be metadata")
    if metadata.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("unsupported certificate schema")
    rows = objects[1:]
    if any(row.get("type") != "phase_certificate_candidate" for row in rows):
        raise ValueError("unexpected non-certificate row")
    return metadata, rows


def verify_rows(rows: Iterable[dict[str, Any]]) -> dict[str, Any]:
    total = certified = unresolved = 0
    failures: list[dict[str, Any]] = []
    zero_interval_failures = 0

    for row in rows:
        total += 1
        zero_lo, zero_hi = dyadic_interval(row["zero_ordinate_interval"])
        if zero_lo <= 0 or zero_hi <= 0:
            zero_interval_failures += 1

        if not row.get("fractional_strip_unique", False):
            unresolved += 1
            continue

        phase_obj = row.get("phase_interval")
        if phase_obj is None:
            failures.append({"row": total, "reason": "unique fractional strip without phase interval"})
            continue

        lo, hi = dyadic_interval(phase_obj)
        wall_n = int(row["wall_n"])
        inferred = inferred_unique_cell(lo, hi, wall_n)
        declared_unique = bool(row.get("cell_unique", False))

        if inferred is None:
            if declared_unique:
                failures.append({"row": total, "reason": "declared unique cell but exact dyadic interval is not strictly contained"})
            else:
                unresolved += 1
            continue

        if not declared_unique:
            failures.append({"row": total, "reason": "exact interval determines a cell but producer marked unresolved"})
            continue

        declared = int(row["cell_index"])
        if declared != inferred:
            failures.append({"row": total, "reason": "declared cell differs from exact inferred cell", "declared": declared, "inferred": inferred})
            continue

        certified += 1

    return {
        "rows": total,
        "certified_rows": certified,
        "unresolved_rows": unresolved,
        "zero_interval_failures": zero_interval_failures,
        "failures": failures,
        "all_declared_cells_exact": not failures,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("bundle", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()

    metadata, rows = load_ndjson(args.bundle)
    summary = verify_rows(rows)
    raw = args.bundle.read_bytes()
    result = {
        "contract": "monster_climbing_gym_rigorous_bundle_exact_dyadic_check",
        "schema_version": SCHEMA_VERSION,
        "bundle_sha256": hashlib.sha256(raw).hexdigest(),
        "producer_metadata": metadata,
        **summary,
        "external_producer_is_agda_proof": False,
        "cell_check_proves_zeta_zero": False,
        "cell_check_proves_monster_specificity": False,
        "cell_check_proves_rh": False,
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")

    if summary["failures"] or summary["zero_interval_failures"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
