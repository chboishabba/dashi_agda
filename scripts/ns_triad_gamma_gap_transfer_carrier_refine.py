#!/usr/bin/env python3
"""Refine a finite NS Gamma-gap carrier by transfer capture and triad closure.

The input is the explicit finite carrier JSON consumed by
``ns_triad_gamma_gap_adversarial_audit.py``.  For each problem/profile carrier,
this tool ranks triads by the observed packet-transfer magnitude

    |c_t| sqrt(p_i p_j p_k),

seeds the smallest set reaching a requested fraction of total transfer mass,
then repeatedly closes the selected mode set under every available relation
``p + q = k`` represented by the carrier's triad list.  The reduced carrier
preserves the original signed coefficients and renormalizes each selected
profile on the retained modes.

This is a finite discovery/export utility.  Transfer capture, energy capture,
and dissipation capture are reported separately.  No theorem or Clay authority
is conferred by a successful finite capture result.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_triad_gamma_gap_transfer_carrier_refine.py"
SCHEMA_VERSION = "1.0.0"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--profile-id", type=str, default=None)
    parser.add_argument("--transfer-capture", type=float, default=0.95)
    parser.add_argument("--max-closure-rounds", type=int, default=64)
    parser.add_argument("--zero-eps", type=float, default=1.0e-15)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _finite_float(value: Any, name: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError(f"{name} must be finite")
    return parsed


def _wavevector(mode: dict[str, Any]) -> tuple[int, int, int]:
    raw = mode.get("wavevector")
    if not isinstance(raw, list) or len(raw) != 3:
        raise ValueError("each mode must contain a length-3 wavevector")
    return tuple(int(x) for x in raw)


def _select_profile(problem: dict[str, Any], profile_id: str | None) -> dict[str, Any]:
    profiles = problem.get("profiles")
    if not isinstance(profiles, list) or not profiles:
        raise ValueError("problem must contain at least one profile")
    if profile_id is None:
        return profiles[0]
    for profile in profiles:
        if str(profile.get("profile_id")) == profile_id:
            return profile
    raise ValueError(f"profile_id not found: {profile_id}")


def _validate_problem(problem: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    modes = problem.get("modes")
    triads = problem.get("triads")
    if not isinstance(modes, list) or not modes:
        raise ValueError("problem must contain non-empty modes")
    if not isinstance(triads, list):
        raise ValueError("problem must contain triads")
    for mode in modes:
        if not isinstance(mode, dict):
            raise ValueError("mode entries must be objects")
        _wavevector(mode)
    n = len(modes)
    for triad in triads:
        if not isinstance(triad, dict):
            raise ValueError("triad entries must be objects")
        left = int(triad["left"])
        right = int(triad["right"])
        out = int(triad["out"])
        if min(left, right, out) < 0 or max(left, right, out) >= n:
            raise ValueError("triad endpoint outside mode carrier")
        p = _wavevector(modes[left])
        q = _wavevector(modes[right])
        k = _wavevector(modes[out])
        if tuple(p[d] + q[d] for d in range(3)) != k:
            raise ValueError(f"triad does not satisfy p+q=k: {(left, right, out)}")
        _finite_float(triad.get("coefficient", 0.0), "coefficient")
    return modes, triads


def _probability(profile: dict[str, Any], mode_count: int, zero_eps: float) -> np.ndarray:
    raw = np.asarray(profile.get("probability"), dtype=np.float64)
    if raw.ndim != 1 or len(raw) != mode_count:
        raise ValueError("profile probability length must match mode count")
    if not np.all(np.isfinite(raw)) or np.any(raw < 0.0):
        raise ValueError("profile probability must be finite and nonnegative")
    total = float(np.sum(raw))
    if total <= zero_eps:
        raise ValueError("profile probability must have positive mass")
    return raw / total


def _triad_transfer_magnitudes(
    triads: list[dict[str, Any]], probability: np.ndarray
) -> np.ndarray:
    amplitude = np.sqrt(np.maximum(probability, 0.0))
    values = []
    for triad in triads:
        left = int(triad["left"])
        right = int(triad["right"])
        out = int(triad["out"])
        coefficient = abs(float(triad.get("coefficient", 0.0)))
        values.append(coefficient * amplitude[left] * amplitude[right] * amplitude[out])
    return np.asarray(values, dtype=np.float64)


def _seed_modes(
    triads: list[dict[str, Any]], magnitudes: np.ndarray, capture: float, zero_eps: float
) -> tuple[set[int], list[int], float]:
    total = float(np.sum(magnitudes))
    if total <= zero_eps:
        return set(), [], 0.0
    target = min(max(float(capture), 0.0), 1.0) * total
    order = sorted(range(len(triads)), key=lambda idx: float(magnitudes[idx]), reverse=True)
    selected_modes: set[int] = set()
    selected_triads: list[int] = []
    running = 0.0
    for idx in order:
        if float(magnitudes[idx]) <= zero_eps:
            continue
        triad = triads[idx]
        selected_modes.update((int(triad["left"]), int(triad["right"]), int(triad["out"])))
        selected_triads.append(idx)
        running += float(magnitudes[idx])
        if running + zero_eps >= target:
            break
    return selected_modes, selected_triads, running / total


def _partner_close(
    selected_modes: set[int], triads: list[dict[str, Any]], max_rounds: int
) -> tuple[set[int], int, bool]:
    selected = set(selected_modes)
    for round_index in range(max(0, int(max_rounds))):
        before = len(selected)
        for triad in triads:
            endpoints = (int(triad["left"]), int(triad["right"]), int(triad["out"]))
            if sum(endpoint in selected for endpoint in endpoints) >= 2:
                selected.update(endpoints)
        if len(selected) == before:
            return selected, round_index + 1, True
    return selected, max(0, int(max_rounds)), False


def _capture_metrics(
    modes: list[dict[str, Any]],
    triads: list[dict[str, Any]],
    probability: np.ndarray,
    magnitudes: np.ndarray,
    selected_modes: set[int],
    zero_eps: float,
) -> dict[str, float]:
    selected_mask = np.asarray([idx in selected_modes for idx in range(len(modes))], dtype=bool)
    energy_capture = float(np.sum(probability[selected_mask]))
    wave_norm2 = np.asarray(
        [sum(component * component for component in _wavevector(mode)) for mode in modes],
        dtype=np.float64,
    )
    total_dissipation = float(np.sum(wave_norm2 * probability))
    selected_dissipation = float(np.sum((wave_norm2 * probability)[selected_mask]))
    retained_transfer = 0.0
    for idx, triad in enumerate(triads):
        endpoints = (int(triad["left"]), int(triad["right"]), int(triad["out"]))
        if all(endpoint in selected_modes for endpoint in endpoints):
            retained_transfer += float(magnitudes[idx])
    total_transfer = float(np.sum(magnitudes))
    return {
        "energy_capture_fraction": energy_capture,
        "dissipation_capture_fraction": (
            selected_dissipation / total_dissipation if total_dissipation > zero_eps else 0.0
        ),
        "transfer_capture_fraction": (
            retained_transfer / total_transfer if total_transfer > zero_eps else 0.0
        ),
    }


def _reduce_problem(
    problem: dict[str, Any],
    profile_id: str | None,
    capture: float,
    max_rounds: int,
    zero_eps: float,
) -> dict[str, Any]:
    modes, triads = _validate_problem(problem)
    reference_profile = _select_profile(problem, profile_id)
    probability = _probability(reference_profile, len(modes), zero_eps)
    magnitudes = _triad_transfer_magnitudes(triads, probability)
    selected_modes, seed_triads, seed_capture = _seed_modes(
        triads, magnitudes, capture, zero_eps
    )
    selected_modes, closure_rounds, closure_converged = _partner_close(
        selected_modes, triads, max_rounds
    )
    if not selected_modes:
        raise ValueError("no nonzero transfer triads available for carrier refinement")

    selected_order = sorted(selected_modes)
    old_to_new = {old: new for new, old in enumerate(selected_order)}
    reduced_modes = [modes[old] for old in selected_order]
    retained_triads: list[dict[str, Any]] = []
    for triad in triads:
        endpoints = (int(triad["left"]), int(triad["right"]), int(triad["out"]))
        if all(endpoint in selected_modes for endpoint in endpoints):
            copied = dict(triad)
            copied["left"] = old_to_new[endpoints[0]]
            copied["right"] = old_to_new[endpoints[1]]
            copied["out"] = old_to_new[endpoints[2]]
            retained_triads.append(copied)

    reduced_profiles: list[dict[str, Any]] = []
    for profile in problem.get("profiles", []):
        p = _probability(profile, len(modes), zero_eps)
        restricted = p[selected_order]
        mass = float(np.sum(restricted))
        if mass <= zero_eps:
            continue
        copied = dict(profile)
        copied["probability"] = [float(value) for value in restricted / mass]
        copied["source_probability_mass_retained"] = mass
        reduced_profiles.append(copied)

    metrics = _capture_metrics(
        modes, triads, probability, magnitudes, selected_modes, zero_eps
    )
    result = dict(problem)
    result["problem_id"] = f"{problem.get('problem_id', 'carrier')}-transfer-closed"
    result["modes"] = reduced_modes
    result["triads"] = retained_triads
    result["profiles"] = reduced_profiles
    result["carrier_refinement"] = {
        "method": "observed_transfer_rank_then_p_plus_q_partner_closure",
        "reference_profile_id": reference_profile.get("profile_id"),
        "requested_transfer_capture": float(capture),
        "seed_transfer_capture_fraction": seed_capture,
        "seed_triad_count": len(seed_triads),
        "selected_mode_count_before_closure": len(
            {endpoint for idx in seed_triads for endpoint in (
                int(triads[idx]["left"]), int(triads[idx]["right"]), int(triads[idx]["out"])
            )}
        ),
        "selected_mode_count_after_closure": len(selected_order),
        "retained_triad_count": len(retained_triads),
        "closure_rounds": closure_rounds,
        "closure_converged": closure_converged,
        **metrics,
        "candidate_only": True,
        "theorem_authority": False,
        "clay_authority": False,
    }
    return result


def main() -> int:
    args = _parse_args()
    if not 0.0 < float(args.transfer_capture) <= 1.0:
        raise ValueError("--transfer-capture must lie in (0, 1]")
    payload = json.loads(args.input_json.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("input JSON must be an object")
    if isinstance(payload.get("problems"), list):
        problems = payload["problems"]
        reduced = [
            _reduce_problem(
                problem,
                args.profile_id,
                args.transfer_capture,
                args.max_closure_rounds,
                args.zero_eps,
            )
            for problem in problems
        ]
        output: dict[str, Any] = {
            "schema_version": SCHEMA_VERSION,
            "producer": SCRIPT_NAME,
            "authority": {
                "candidate_only": True,
                "theorem_authority": False,
                "clay_authority": False,
                "promoted": False,
            },
            "problems": reduced,
        }
    else:
        output = _reduce_problem(
            payload,
            args.profile_id,
            args.transfer_capture,
            args.max_closure_rounds,
            args.zero_eps,
        )
        output["producer"] = SCRIPT_NAME
        output["schema_version"] = SCHEMA_VERSION
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(output, indent=2 if args.pretty else None, sort_keys=True, allow_nan=False)
        + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
