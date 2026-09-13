#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


OUTPUT_STEM = "continuous_oscillator_synthetic"
OSCILLATOR_COUNTS = [3, 6, 9]
FAIL_CLOSED_FLAGS = {
    "neuroscience_interpretation_promoted": False,
    "memory_mechanism_promoted": False,
    "hebbian_identity_promoted": False,
    "kuramoto_identity_promoted": False,
    "cognitive_dissonance_identity_promoted": False,
    "empirical_brain_fit_promoted": False,
    "three_six_nine_superiority_promoted": False,
    "quantum_interpretation_promoted": False,
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the bounded synthetic continuous-oscillator diagnostic."
    )
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args()


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    args = parse_args()
    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    json_path = out_dir / f"{OUTPUT_STEM}.json"
    trajectories_path = out_dir / "continuous_oscillator_trajectories.csv"
    comparison_path = out_dir / "continuous_oscillator_comparison.csv"
    markdown_path = out_dir / f"{OUTPUT_STEM}.md"

    payload: dict[str, Any] = {
        "diagnostic": OUTPUT_STEM,
        "schema_version": 1,
        "status": "synthetic_only_no_promotion",
        "oscillator_counts": OSCILLATOR_COUNTS,
        "promotion": {
            "state": "blocked",
            "flags": FAIL_CLOSED_FLAGS,
        },
        "runs": [],
        "output_paths": {
            "json": str(json_path),
            "trajectories_csv": str(trajectories_path),
            "comparison_csv": str(comparison_path),
            "markdown": str(markdown_path),
        },
    }

    write_csv(trajectories_path, ["oscillator_count", "seed", "step"], [])
    write_csv(comparison_path, ["oscillator_count", "seed"], [])
    markdown_path.write_text(
        "# Continuous oscillator synthetic diagnostic\n\n"
        "Status: `synthetic_only_no_promotion`\n",
        encoding="utf-8",
    )
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
