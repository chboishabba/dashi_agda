#!/usr/bin/env python3
"""Falsification-first audit for the canonical Navier--Stokes Gamma gap.

The exact finite identity formalized in Agda is

    Gamma_K = E_{K,+} * A_K / (2 nu D_K)
            = max(Q_K, 0) / (2 nu D_K).

The script evaluates the identity on finite triad carriers and searches the
normalized profile simplex for sampled counterexamples.  It is empirical,
finite-dimensional, fail-closed, and non-promoting.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Sequence

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ns_triad_gamma_gap_core import (  # noqa: E402
    Constraints,
    Mode,
    Problem,
    SearchConfig,
    Triad,
    finite,
    normalize_probability,
    parse_wavevector,
)
from ns_triad_gamma_gap_search import audit_problem, window_rows  # noqa: E402

SCHEMA_VERSION = "1.0.0"
SCRIPT_NAME = "scripts/ns_triad_gamma_gap_adversarial_audit.py"
AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "promoted": False,
}


def parse_problem(
    payload: dict[str, Any], default_viscosity: float | None = None
) -> Problem:
    modes_payload = payload.get("modes")
    triads_payload = payload.get("triads")
    if not isinstance(modes_payload, list) or not isinstance(triads_payload, list):
        raise ValueError("problem requires modes and triads lists")

    modes_list: list[Mode] = []
    for index, mode in enumerate(modes_payload):
        if not isinstance(mode, dict):
            raise ValueError(f"modes[{index}] must be an object")
        wavevector = parse_wavevector(
            mode.get("wavevector"), f"modes[{index}].wavevector"
        )
        default_weight = sum(coordinate * coordinate for coordinate in wavevector)
        modes_list.append(
            Mode(
                wavevector=wavevector,
                dissipation_weight=finite(
                    mode.get("dissipation_weight", default_weight),
                    f"modes[{index}].dissipation_weight",
                ),
            )
        )

    triads_list: list[Triad] = []
    for index, triad in enumerate(triads_payload):
        if not isinstance(triad, dict):
            raise ValueError(f"triads[{index}] must be an object")
        triads_list.append(
            Triad(
                left=int(triad["left"]),
                right=int(triad["right"]),
                out=int(triad["out"]),
                coefficient=finite(
                    triad["coefficient"], f"triads[{index}].coefficient"
                ),
                orbit_id=(
                    None if triad.get("orbit_id") is None else str(triad["orbit_id"])
                ),
            )
        )

    viscosity = payload.get("viscosity", default_viscosity)
    if viscosity is None:
        raise ValueError("viscosity must be provided in the problem or command line")
    profiles = payload.get("profiles", [])
    if not isinstance(profiles, list) or any(
        not isinstance(profile, dict) for profile in profiles
    ):
        raise ValueError("profiles must be a list of objects")
    return Problem(
        problem_id=str(payload.get("problem_id", "unnamed")),
        viscosity=finite(viscosity, "viscosity"),
        modes=tuple(modes_list),
        triads=tuple(triads_list),
        convention=str(payload.get("convention", "left_plus_right_equals_out")),
        coefficient_semantics=str(
            payload.get(
                "coefficient_semantics", "explicit_signed_transfer_coefficient"
            )
        ),
        profiles=tuple(profiles),
    )


def load_problems(
    path: Path, default_viscosity: float | None = None
) -> list[Problem]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("input JSON must be an object")
    problems_payload = payload.get("problems", [payload])
    if not isinstance(problems_payload, list) or not problems_payload:
        raise ValueError("problems must be a nonempty list")
    if any(not isinstance(problem, dict) for problem in problems_payload):
        raise ValueError("every problem must be an object")
    return [parse_problem(problem, default_viscosity) for problem in problems_payload]


def load_frame_surrogate_problems(
    raw_archive: Path,
    *,
    viscosity: float,
    frame: int | None,
    frame_limit: int | None,
    top_k: int,
    pool_multiplier: int,
    shells: Sequence[int],
    triad_sample_limit: int,
    zero_eps: float,
) -> list[Problem]:
    """Adapt the existing phase-coherence carrier into discovery problems."""

    from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
    from ns_orbit_phase_coherence_scan import (  # type: ignore
        _collect_modes,
        _frame_velocity,
        _load_raw_bundle,
        _scalar_vorticity_spectrum,
    )
    from ns_triad_cocycle_floor_scan import _mode_shell_filter  # type: ignore
    from ns_triad_frame_stability_scan import _build_frame_surface  # type: ignore

    warnings: list[str] = []
    bundle = _load_raw_bundle(raw_archive, warnings)
    selected_frames = _frame_indices(bundle.frame_count, frame, frame_limit)
    selected_shells = sorted({int(shell) for shell in shells if int(shell) > 0})
    if not selected_shells:
        raise ValueError("at least one positive --shell is required")

    problems: list[Problem] = []
    for snapshot in selected_frames:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        collected = _collect_modes(
            spectrum,
            top_k=int(top_k),
            zero_eps=float(zero_eps),
            pool_multiplier=int(pool_multiplier),
        )
        for shell_n in selected_shells:
            shell_modes = _mode_shell_filter(collected, shell_n)
            if not shell_modes:
                continue
            triad_records, _frame_metrics = _build_frame_surface(
                shell_modes,
                zero_eps=float(zero_eps),
                triad_sample_limit=int(triad_sample_limit),
            )
            modes = tuple(
                Mode(
                    wavevector=tuple(int(value) for value in mode.key),
                    dissipation_weight=float(
                        sum(int(value) ** 2 for value in mode.key)
                    ),
                )
                for mode in shell_modes
            )
            triads = tuple(
                Triad(
                    left=int(triad.left),
                    right=int(triad.right),
                    out=int(triad.out),
                    coefficient=float(triad.coherence),
                )
                for triad in triad_records
            )
            amplitude_squared = np.asarray(
                [float(mode.amplitude) ** 2 for mode in shell_modes],
                dtype=np.float64,
            )
            profiles: tuple[dict[str, Any], ...] = ()
            if float(np.sum(amplitude_squared)) > float(zero_eps):
                observed = normalize_probability(amplitude_squared, zero_eps)
                profiles = (
                    {
                        "profile_id": f"observed-frame-{snapshot}-shell-{shell_n}",
                        "trajectory_id": f"raw:{raw_archive}",
                        "time": float(snapshot),
                        "duration": 1.0,
                        "cutoff": int(shell_n),
                        "probability": [float(value) for value in observed],
                    },
                )
            problems.append(
                Problem(
                    problem_id=f"frame-{snapshot}-shell-{shell_n}",
                    viscosity=float(viscosity),
                    modes=modes,
                    triads=triads,
                    coefficient_semantics=(
                        "phase_coherence_surrogate_cos_phi_left_plus_phi_right_minus_phi_out; "
                        "not_physical_fourier_transfer"
                    ),
                    profiles=profiles,
                )
            )
    if not problems:
        raise ValueError("raw archive adapter produced no nonempty shell carriers")
    return problems


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--input-json", type=Path)
    source.add_argument("--raw-archive", type=Path)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--viscosity", type=float, default=None)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=1)
    parser.add_argument("--top-k", type=int, default=48)
    parser.add_argument("--pool-multiplier", type=int, default=24)
    parser.add_argument("--triad-sample-limit", type=int, default=8)
    parser.add_argument("--shell", action="append", type=int, dest="shells")
    parser.add_argument("--target-eta", type=float, default=0.05)
    parser.add_argument("--random-samples", type=int, default=512)
    parser.add_argument("--local-steps", type=int, default=128)
    parser.add_argument("--seed", action="append", type=int, dest="seeds")
    parser.add_argument("--zero-eps", type=float, default=1.0e-12)
    parser.add_argument("--max-neff", type=float, default=None)
    parser.add_argument("--max-radial-variance", type=float, default=None)
    parser.add_argument("--min-peak-mass", type=float, default=None)
    parser.add_argument("--max-dissipation", type=float, default=None)
    parser.add_argument("--cancellation-cap", type=float, default=0.75)
    parser.add_argument("--envelope-cap", type=float, default=0.75)
    parser.add_argument("--window-size", action="append", type=int, dest="window_sizes")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not 0.0 < args.target_eta < 1.0:
        raise ValueError("--target-eta must lie in (0, 1)")
    config = SearchConfig(
        target_eta=float(args.target_eta),
        random_samples=max(0, int(args.random_samples)),
        local_steps=max(0, int(args.local_steps)),
        seeds=tuple(args.seeds if args.seeds is not None else (0, 1, 2)),
        zero_eps=float(args.zero_eps),
        constraints=Constraints(
            max_neff=args.max_neff,
            max_radial_variance=args.max_radial_variance,
            min_peak_mass=args.min_peak_mass,
            max_dissipation=args.max_dissipation,
        ),
        cancellation_cap=float(args.cancellation_cap),
        envelope_cap=float(args.envelope_cap),
        window_sizes=tuple(
            args.window_sizes if args.window_sizes is not None else (2, 4, 8)
        ),
    )
    if args.input_json is not None:
        problems = load_problems(args.input_json, args.viscosity)
        source_mode = "explicit-transfer-json"
    else:
        if args.viscosity is None:
            raise ValueError("--viscosity is required with --raw-archive")
        problems = load_frame_surrogate_problems(
            args.raw_archive,
            viscosity=float(args.viscosity),
            frame=args.frame,
            frame_limit=args.frame_limit,
            top_k=args.top_k,
            pool_multiplier=args.pool_multiplier,
            shells=args.shells if args.shells is not None else (2, 3, 4, 5),
            triad_sample_limit=args.triad_sample_limit,
            zero_eps=config.zero_eps,
        )
        source_mode = "raw-frame-phase-coherence-surrogate"

    results = [audit_problem(problem, config) for problem in problems]
    counterexample_count = sum(
        int(result["target_counterexample_count"]) for result in results
    )
    observed_rows = [
        row
        for result in results
        for row in result.get("input_profile_rows", [])
    ]
    observed_windows = window_rows(
        observed_rows, config.window_sizes, config.target_eta
    )
    interval_counterexample_count = sum(
        1 for row in observed_windows if row["target_counterexample"]
    )
    worst_observed_window = max(
        observed_windows,
        key=lambda row: float(row["average_gamma"]),
        default=None,
    )
    payload = {
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "target": "integral_I Gamma_K,p,R(t) dt <= (1-eta) |I|",
        "source_mode": source_mode,
        "interpretation": (
            "Falsification-first finite audit only. no_counterexample_sampled is not a proof, "
            "and coherence-surrogate coefficients are not continuum Navier-Stokes transfer authority."
        ),
        "config": {
            "target_eta": config.target_eta,
            "random_samples_per_seed": config.random_samples,
            "local_steps": config.local_steps,
            "seeds": list(config.seeds),
            "constraints": config.constraints.__dict__,
            "cancellation_cap": config.cancellation_cap,
            "envelope_cap": config.envelope_cap,
            "window_sizes": list(config.window_sizes),
        },
        "problem_count": len(results),
        "sampled_counterexample_count": counterexample_count,
        "no_counterexample_sampled": counterexample_count == 0,
        "observed_window_count": len(observed_windows),
        "sampled_interval_counterexample_count": interval_counterexample_count,
        "no_interval_counterexample_sampled": interval_counterexample_count == 0,
        "worst_observed_window": worst_observed_window,
        "results": results,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(
            payload,
            sort_keys=True,
            indent=2 if args.pretty else None,
            allow_nan=False,
        )
        + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
