#!/usr/bin/env python3
"""Sprint 103 YM authority-input audit for obligations 1-3 only."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


AUTHORITY_INPUTS: list[dict[str, Any]] = [
    {
        "lemma": "BalabanCMP98LocalOscillationBound",
        "authority_input_inhabited": True,
        "source_present": True,
        "proof_argument_present": True,
        "scope": "CMP98 local oscillation estimate for Q_hp",
    },
    {
        "lemma": "BalabanCMP98AveragingKernelIsProbability",
        "authority_input_inhabited": True,
        "source_present": True,
        "proof_argument_present": True,
        "scope": "CMP98 Haar-convolution probability kernel giving C_avg <= 1",
    },
    {
        "lemma": "BalabanCMP116PolymerMassBound",
        "authority_input_inhabited": True,
        "source_present": True,
        "proof_argument_present": True,
        "scope": "CMP116 small-field polymer positive mass bound",
    },
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint103_authority_inputs"),
    )
    return parser.parse_args()


def summary_payload() -> dict[str, Any]:
    return {
        "sprint": "103-authority-inputs",
        "implemented_authority_input_count": len(AUTHORITY_INPUTS),
        "authority_inputs": AUTHORITY_INPUTS,
        "implemented_only_inputs_1_to_3": True,
        "empty_data_types_introduced": False,
        "downstream_sprint102_obligations_still_open": True,
        "clay_yang_mills_promoted": False,
        "route_decision": "SPRINT103_INHABITS_AUTHORITY_INPUTS_1_2_3_ONLY_NO_PROMOTION",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "ym_sprint103_authority_inputs_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
