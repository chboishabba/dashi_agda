#!/usr/bin/env python3
"""Create a deterministic Latin-hypercube manifest for quotient-profile search.

The manifest is deliberately non-executing.  Stage A records static,
positive-signed-chi admissibility trials; Stage B is reserved for a selected
subset evolved over a short parabolic window; only survivors can be promoted
to a full-window run.  This avoids treating manually named profile axes as an
adversarial search.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=64)
    parser.add_argument("--seed", type=int, default=20260717)
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--nu", type=float, default=1.0e-3)
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--critical-mass", type=float, default=1.0)
    parser.add_argument("--chi-target", type=float, default=0.1584541238)
    parser.add_argument("--chi-tolerance", type=float, default=0.05)
    parser.add_argument("--chi-attempts", type=int, default=16)
    parser.add_argument("--short-window-c", type=float, default=0.05)
    parser.add_argument("--output-json", type=Path,
                        default=Path("scripts/data/outputs/ns_interaction_closure_production/ns_profile_positive_chi_lhs_manifest.json"))
    return parser.parse_args()


def lhs(rng: np.random.Generator, count: int, lower: float, upper: float, logarithmic: bool = False) -> np.ndarray:
    unit = (rng.permutation(count) + rng.random(count)) / count
    if logarithmic:
        return np.exp(math.log(lower) + unit * (math.log(upper) - math.log(lower)))
    return lower + unit * (upper - lower)


def main() -> None:
    args = parse_args()
    if args.count <= 0 or args.nu <= 0.0 or args.critical_mass <= 0.0:
        raise ValueError("count, nu, and critical mass must be positive")
    rng = np.random.default_rng(args.seed)
    angular = lhs(rng, args.count, 0.22, 2.6, logarithmic=True)
    radial = lhs(rng, args.count, 0.18, 1.0, logarithmic=True)
    helicity = lhs(rng, args.count, -0.9, 0.9)
    coherence = lhs(rng, args.count, 0.0, 1.0)
    entries = []
    for index in range(args.count):
        shape = {
            "angular_width": float(angular[index]),
            "radial_log_width": float(radial[index]),
            "helicity_bias": float(helicity[index]),
            "spatial_coherence": float(coherence[index]),
        }
        common = [
            "--n", str(args.n), "--nu", str(args.nu), "--target-shell", str(args.target_shell),
            "--critical-mass", str(args.critical_mass), "--angular-width", str(shape["angular_width"]),
            "--radial-log-width", str(shape["radial_log_width"]), "--helicity-bias", str(shape["helicity_bias"]),
            "--spatial-coherence", str(shape["spatial_coherence"]), "--chi-sign", "positive",
            "--chi-target", str(args.chi_target), "--chi-tolerance", str(args.chi_tolerance),
            "--chi-attempts", str(args.chi_attempts), "--target-dominance-min", "0.8",
            "--seed", str(args.seed + index * 1009),
        ]
        entries.append({
            "id": f"lhs-{index:03d}", "shape": shape,
            "stage_a_static_arguments": common,
            "stage_b_short_survival_additions": [
                "--evolve", "--backend", "gpu", "--window-c", str(args.short_window_c),
                "--selection-objective", "short-survival", "--require-positive-short-input",
            ],
            "stage_c_full_window_additions": ["--evolve", "--backend", "gpu", "--window-c", "1"],
        })
    payload = {
        "contract": "ns_normalized_profile_latin_hypercube_manifest_nonexecuting",
        "authority": {"empirical_non_promoting": True, "theorem_authority": False, "clay_authority": False},
        "design": {
            "kind": "four-axis Latin hypercube over quotient-shape coordinates",
            "axes": ["angular_width", "radial_log_width", "helicity_bias", "spatial_coherence"],
            "signed_chi_gate": "positive", "target_dominance_min": 0.8,
            "stages": ["static admissibility", "short endpoint survival", "full-window survivor"],
        },
        "entries": entries,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
