#!/usr/bin/env python3
"""Emit a deterministic Shahmurov claim-intake JSON receipt."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_shahmurov_claim_intake.py"
CONTRACT = "ns_shahmurov_claim_intake"
STATUS = "fail-closed"

DEFAULT_OUTPUT = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260619"
    / "ns_shahmurov_claim_intake_20260619.json"
)

PART_I_ARXIV_ID = "2605.01875"
PART_II_ARXIV_ID = "2605.01873"
REQUIRED_MANUAL_CHECKS = [
    "zero_defect_rigidity",
    "passive_strain_visibility",
    "endpoint_strictness",
    "finite_overlap_descendants",
    "part_i_dependency",
]


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output JSON path. Defaults to the repository-side claim intake receipt.",
    )
    return parser.parse_args()


def _receipt(output_path: Path) -> dict[str, Any]:
    source_metadata = [
        {
            "arxiv_id": PART_I_ARXIV_ID,
            "source_status": "claimed_external_preprint",
            "version": "v3",
            "date": "2026-05-15",
            "role": "part_i_axisymmetric_with_swirl",
        },
        {
            "arxiv_id": PART_II_ARXIV_ID,
            "source_status": "claimed_external_preprint",
            "version": "v2",
            "date": "2026-05-15",
            "role": "part_ii_full_system_front_end",
        },
    ]

    return {
        "C": SCRIPT_NAME,
        "F": "The receipt records claim intake only and does not promote any proof or route.",
        "G": "Peer review, Clay promotion, and route supersession are all held false.",
        "L": "Claim metadata is recorded deterministically; manual checks remain required.",
        "O": "Record deterministic Shahmurov claim-intake metadata for the NS route.",
        "P": "FAIL_CLOSED_NS_SHAHMUROV_CLAIM_INTAKE",
        "R": "Capture claim metadata, version/date provenance, and fail-closed intake gates.",
        "S": "Write a stable JSON receipt with explicit false gates and required manual checks.",
        "contract": CONTRACT,
        "status": STATUS,
        "output_json": str(output_path),
        "claim_intake": {
            "route_name": "Shahmurov two-paper first-threshold route",
            "arxiv_ids": [PART_I_ARXIV_ID, PART_II_ARXIV_ID],
            "source_metadata": source_metadata,
            "fail_closed_gates": {
                "peer_review_verified": False,
                "clay_promotion": False,
                "dashi_route_superseded": False,
                "required_manual_checks": REQUIRED_MANUAL_CHECKS,
            },
        },
    }


def main() -> int:
    args = _parse_args()
    output_path = args.output
    output_path.parent.mkdir(parents=True, exist_ok=True)

    receipt = _receipt(output_path)
    text = json.dumps(receipt, sort_keys=True, separators=(",", ":")) + "\n"
    output_path.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
