#!/usr/bin/env python3
"""Emit a non-executing local-residence manifest around one saved NS state.

This manifest is intentionally state-anchored: every candidate starts from
the same reproducible finite Fourier survivor, applies one deterministic local
deformation, restores finite H^(1/2) mass, and must pass the positive signed
chi and target-dominance gates before any GPU evolution.  It does not claim a
continuum tangent space, a profile-uniform law, or a Navier--Stokes theorem.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DEFAULT_STATE = Path(
    "scripts/data/outputs/ns_interaction_closure_production/"
    "N32j2_profile_positive_chi_attempt1_state.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_interaction_closure_production/"
    "ns_profile_positive_chi_local_perturbation_manifest.json"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state-input", type=Path, default=DEFAULT_STATE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--nu", type=float, default=1.0e-3)
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--critical-mass", type=float, default=1.0)
    parser.add_argument("--chi-target", type=float, default=0.16518290321070614)
    parser.add_argument("--chi-tolerance", type=float, default=0.05)
    parser.add_argument("--target-dominance-min", type=float, default=0.8)
    parser.add_argument("--base-epsilon", type=float, default=0.02)
    parser.add_argument("--seed", type=int, default=20260719)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.base_epsilon <= 0.0 or args.chi_tolerance <= 0.0:
        raise ValueError("base epsilon and chi tolerance must be positive")
    if not args.state_input.is_file():
        raise FileNotFoundError(f"missing saved survivor: {args.state_input}")
    epsilon_multipliers = (-2.0, -1.0, -0.5, 0.5, 1.0, 2.0)
    # Two independent tangent realisations are useful only for directions that
    # explicitly use random per-mode signs/phases.  This yields 42 candidates:
    # 6 each for angular/radial/coherence, and 12 each for phase/helicity.
    realisation_count = {"phase": 2, "coherence": 1, "angular": 1, "radial": 1, "helicity": 2}
    entries: list[dict[str, object]] = []
    ordinal = 0
    for direction in ("phase", "coherence", "angular", "radial", "helicity"):
        for realisation in range(realisation_count[direction]):
            for multiplier in epsilon_multipliers:
                perturb_seed = args.seed + 1009 * ordinal + 97 * realisation
                epsilon = args.base_epsilon * multiplier
                identity = f"{direction}-r{realisation}-e{epsilon:+.4f}".replace("+", "p").replace("-", "m")
                common = [
                    "--n", str(args.n), "--nu", str(args.nu), "--target-shell", str(args.target_shell),
                    "--critical-mass", str(args.critical_mass), "--state-input", str(args.state_input),
                    "--state-perturbation", direction, "--perturb-epsilon", str(epsilon),
                    "--perturb-seed", str(perturb_seed), "--chi-sign", "positive",
                    "--chi-target", str(args.chi_target), "--chi-tolerance", str(args.chi_tolerance),
                    "--require-chi-tolerance", "--target-dominance-min", str(args.target_dominance_min),
                ]
                entries.append({
                    "id": identity,
                    "direction": direction,
                    "realisation": realisation,
                    "epsilon": epsilon,
                    "perturb_seed": perturb_seed,
                    "stage_a_static_arguments": common,
                    "stage_b_short_residence_additions": [
                        "--evolve", "--backend", "gpu", "--window-c", "0.05",
                        "--checkpoint-fractions", "0,0.5,1",
                    ],
                    "stage_c_medium_residence_additions": [
                        "--evolve", "--backend", "gpu", "--window-c", "0.10",
                        "--checkpoint-fractions", "0,0.25,0.5,0.75,1",
                    ],
                    "stage_d_parabolic_window_additions": [
                        "--evolve", "--backend", "gpu", "--window-c", "0.25",
                        "--checkpoint-fractions", "0,0.2,0.4,0.6,0.8,1",
                    ],
                })
                ordinal += 1
    payload = {
        "contract": "state_anchored_local_perturbation_manifest_nonexecuting",
        "authority": {"empirical_non_promoting": True, "theorem_authority": False, "clay_authority": False},
        "reference_state": str(args.state_input),
        "design": {
            "candidate_count": len(entries),
            "directions": ["phase", "coherence", "angular", "radial", "helicity"],
            "epsilon_multipliers": list(epsilon_multipliers),
            "critical_mass": args.critical_mass,
            "admissibility": {
                "signed_chi": "positive",
                "chi_target": args.chi_target,
                "chi_tolerance": args.chi_tolerance,
                "target_dominance_min": args.target_dominance_min,
            },
            "promotion_rule": "static admissibility -> .05T residence -> .10T residence -> .25T only for genuine survivors",
        },
        "entries": entries,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
