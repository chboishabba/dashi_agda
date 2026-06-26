#!/usr/bin/env python3
"""Generate the PM Volume I / Dashi comparison crosswalk."""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "outputs" / "pm_dashi_crosswalk.json"


def numbered_row(n: int) -> dict[str, object]:
    if 1 <= n <= 5:
        module = "DASHI.Foundations.PMDeductionBridge"
        status = "checked-dashi-socket"
    elif 20 <= n <= 43:
        module = "DASHI.Core.RelationAlgebraCore"
        status = "checked-dashi-socket"
    elif 60 <= n <= 80:
        module = "DASHI.Foundations.PMCardinalProlegomenaCore"
        status = "candidate-socket"
    else:
        module = "DASHI.Foundations.PMVol1ChapterIndexCore"
        status = "candidate-inventory-only"

    return {
        "pm_chapter": f"*{n}",
        "pm_package_id": f"pm-vol1-star-{n:02d}",
        "jmd_lean_package_id": f"jmd-pm-vol1-star-{n:02d}",
        "dashi_module": module,
        "dashi_status": status,
        "candidate_only": True,
        "proposition_completion_authority": False,
        "exact_pm_notation_authority": False,
    }


def appendix_row(n: int, module: str, status: str) -> dict[str, object]:
    return {
        "pm_chapter": f"appendix-*{n}",
        "pm_package_id": f"pm-vol1-appendix-star-{n}",
        "jmd_lean_package_id": f"jmd-pm-vol1-appendix-star-{n}",
        "dashi_module": module,
        "dashi_status": status,
        "candidate_only": True,
        "proposition_completion_authority": False,
        "exact_pm_notation_authority": False,
    }


def build_crosswalk() -> dict[str, object]:
    rows = [numbered_row(n) for n in range(1, 98)]
    rows.extend(
        [
            appendix_row(8, "DASHI.Foundations.PMDeductionBridge", "external-substrate-boundary"),
            appendix_row(89, "DASHI.Foundations.PMCardinalProlegomenaCore", "candidate-socket"),
            appendix_row(99, "DASHI.Foundations.PMVol1ChapterIndexCore", "candidate-inventory-only"),
        ]
    )
    return {
        "schema": "pm-dashi-crosswalk-v1",
        "volume": "Principia Mathematica Volume I",
        "row_count": len(rows),
        "authority": {
            "comparison_bridge_only": True,
            "direct_pm_formalization_authority": False,
            "proposition_corpus_authority": False,
            "cardinal_arithmetic_authority": False,
            "exact_pm_notation_authority": False,
        },
        "rows": rows,
    }


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    payload = build_crosswalk()
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
