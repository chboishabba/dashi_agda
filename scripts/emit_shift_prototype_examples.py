#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

EXAMPLES_DIR = Path("scripts/examples")
CANONICAL_EXAMPLE_FILENAMES = {
    "near_miss_state.json",
    "head_on_state.json",
}

CANONICAL_SHIFT_SOURCE = {
    "module": "DASHI/Geometry/ShiftLorentzEmergenceInstance.agda",
    "state_symbol": "canonicalShiftStateWitness",
    "basin_symbol": "ShiftInBasin",
    "bridge_symbol": "canonicalShiftGeometryBridge",
    "seed_origin": "DASHI/Physics/Signature31InstanceShiftZ.agda::shell1SeedTrit",
}


def canonical_near_miss_state() -> dict[str, Any]:
    return {
        "trace_id": "near-miss-shell1-emitted",
        "delta": [1.0, 0.0, 0.0, 0.0],
        "coarse_head": [1.0],
        "mdl_level": 0.0,
        "photon_energy": 0.22,
        "provenance": {
            **CANONICAL_SHIFT_SOURCE,
            "derivation": "canonical shell1 numeric representative",
        },
        "admissibility": {
            "basin_expected": True,
            "coarse_head_matches_shell1": True,
            "notes": [
                "Numeric representative of the shell1 trit seed pos, zer, zer, zer.",
                "Does not execute Agda; anchors the prototype state to the named canonical witness."
            ],
        },
    }


def admissible_head_on_template() -> dict[str, Any]:
    return {
        "trace_id": "head-on-shell1-emitted",
        "delta": [0.2, 0.65, 0.45, 0.25],
        "coarse_head": [1.0],
        "mdl_level": 1.3,
        "photon_energy": 0.22,
        "provenance": {
            **CANONICAL_SHIFT_SOURCE,
            "derivation": "basin-preserving perturbation template from canonical shell1 basis",
        },
        "admissibility": {
            "basin_expected": True,
            "coarse_head_matches_shell1": True,
            "notes": [
                "Uses the same coarse-head basin condition as the canonical shell1 source.",
                "Perturbation is explanatory only; it is not claimed to be a traced execution state."
            ],
        },
    }


def emit_examples(output_dir: Path) -> list[Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    outputs = [
        (output_dir / "near_miss_state.json", canonical_near_miss_state()),
        (output_dir / "head_on_state.json", admissible_head_on_template()),
    ]
    written: list[Path] = []
    for path, payload in outputs:
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        written.append(path)
    return written


def _emitter_is_newer(target: Path) -> bool:
    emitter_path = Path(__file__)
    if not target.exists():
        return True
    return emitter_path.stat().st_mtime > target.stat().st_mtime


def ensure_canonical_example(path: Path) -> Path:
    if path.name not in CANONICAL_EXAMPLE_FILENAMES:
        return path
    if path.parent != EXAMPLES_DIR:
        return path
    if _emitter_is_newer(path):
        emit_examples(EXAMPLES_DIR)
    return path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Emit prototype example states from the canonical Dashi shift path"
    )
    parser.add_argument(
        "--output-dir",
        default="scripts/examples",
        help="Directory where example state JSON files will be written",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    written = emit_examples(Path(args.output_dir))
    payload = {
        "emitter": "shift-prototype-example-emitter",
        "written": [str(path) for path in written],
        "source": CANONICAL_SHIFT_SOURCE,
        "notes": [
            "Examples are emitted from the canonical shell1 shift-path witness and a basin-preserving perturbation template.",
            "This script does not execute Agda; it materializes prototype JSON fixtures with explicit provenance."
        ],
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
