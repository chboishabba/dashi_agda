#!/usr/bin/env python3
"""Exact finite optimizer for the Round-40 singleton coefficient budget.

The input is a JSON object with a ``candidates`` array.  Every candidate must
contain a stable ``name``, an ``admissible`` boolean, and exact rational strings
``raw_localization_cost`` and ``multiplier_defect_cost``.  Decimal floats are
rejected: the producer must expose the exact coefficient ledger.

The script chooses the least admissible total using ``fractions.Fraction`` and
emits a fail-closed JSON certificate consumed by review/checker tooling.  It
never invents the old 27+28 split.  If no candidate fits 55/18874368 it emits a
no-fit dual lower bound equal to the least admissible total and exits 2.
"""
from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

BUDGET = Fraction(55, 18_874_368)
RATIONAL_RE = re.compile(r"^[+-]?[0-9]+(?:/[1-9][0-9]*)?$")


@dataclass(frozen=True)
class Candidate:
    name: str
    admissible: bool
    raw: Fraction
    multiplier: Fraction
    metadata: dict[str, Any]

    @property
    def total(self) -> Fraction:
        return self.raw + self.multiplier


def parse_fraction(value: Any, field: str) -> Fraction:
    if not isinstance(value, str) or not RATIONAL_RE.fullmatch(value.strip()):
        raise ValueError(
            f"{field} must be an exact integer or p/q string; got {value!r}"
        )
    result = Fraction(value)
    if result < 0:
        raise ValueError(f"{field} must be nonnegative; got {value!r}")
    return result


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def load_candidates(path: Path) -> list[Candidate]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    raw_candidates = payload.get("candidates")
    if not isinstance(raw_candidates, list) or not raw_candidates:
        raise ValueError("input must contain a nonempty 'candidates' array")

    seen: set[str] = set()
    candidates: list[Candidate] = []
    for index, item in enumerate(raw_candidates):
        if not isinstance(item, dict):
            raise ValueError(f"candidate {index} is not an object")
        name = item.get("name")
        if not isinstance(name, str) or not name.strip():
            raise ValueError(f"candidate {index} has no stable name")
        if name in seen:
            raise ValueError(f"duplicate candidate name: {name}")
        seen.add(name)
        admissible = item.get("admissible")
        if not isinstance(admissible, bool):
            raise ValueError(f"candidate {name}: admissible must be boolean")
        raw = parse_fraction(
            item.get("raw_localization_cost"),
            f"candidate {name}.raw_localization_cost",
        )
        multiplier = parse_fraction(
            item.get("multiplier_defect_cost"),
            f"candidate {name}.multiplier_defect_cost",
        )
        metadata = item.get("metadata", {})
        if not isinstance(metadata, dict):
            raise ValueError(f"candidate {name}: metadata must be an object")
        candidates.append(Candidate(name, admissible, raw, multiplier, metadata))
    return candidates


def make_certificate(candidates: list[Candidate]) -> tuple[dict[str, Any], int]:
    admissible = [candidate for candidate in candidates if candidate.admissible]
    if not admissible:
        raise ValueError("candidate family has no admissible assignment")

    selected = min(admissible, key=lambda c: (c.total, c.raw, c.name))
    comparisons = [
        {
            "candidate": candidate.name,
            "candidate_total": fraction_text(candidate.total),
            "selected_le_candidate": selected.total <= candidate.total,
            "exact_difference": fraction_text(candidate.total - selected.total),
        }
        for candidate in sorted(admissible, key=lambda c: c.name)
    ]

    base = {
        "schema": "dashi.ym.round40.singleton-optimization.v1",
        "budget": fraction_text(BUDGET),
        "physicalParameterAssignment": selected.name,
        "rawLocalizationCostExact": fraction_text(selected.raw),
        "multiplierDefectCostExact": fraction_text(selected.multiplier),
        "singletonTotalCostExact": fraction_text(selected.total),
        "globalMinimalityComparisons": comparisons,
        "metadata": selected.metadata,
    }

    if selected.total <= BUDGET:
        base.update(
            {
                "status": "fit",
                "singletonTotalBelowBudget": True,
                "budgetSlackExact": fraction_text(BUDGET - selected.total),
            }
        )
        return base, 0

    base.update(
        {
            "status": "no_fit",
            "singletonTotalBelowBudget": False,
            "certifiedLowerBound": fraction_text(selected.total),
            "lowerBoundStrictlyExceedsBudget": selected.total > BUDGET,
            "budgetDeficitExact": fraction_text(selected.total - BUDGET),
        }
    )
    return base, 2


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--expect", choices=("fit", "no-fit", "either"), default="either"
    )
    args = parser.parse_args()

    candidates = load_candidates(args.input)
    certificate, status = make_certificate(candidates)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    actual = "fit" if status == 0 else "no-fit"
    if args.expect != "either" and args.expect != actual:
        raise SystemExit(
            f"expected {args.expect}, optimizer produced {actual}: {args.output}"
        )

    print(
        f"[{actual}] selected={certificate['physicalParameterAssignment']} "
        f"total={certificate['singletonTotalCostExact']} "
        f"budget={certificate['budget']}"
    )
    return status


if __name__ == "__main__":
    raise SystemExit(main())
