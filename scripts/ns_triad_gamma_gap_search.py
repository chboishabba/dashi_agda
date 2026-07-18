"""Adversarial simplex and interval search for the NS Gamma-gap audit."""

from __future__ import annotations

import math
from typing import Any, Iterable

import numpy as np

from ns_triad_gamma_gap_core import (
    Problem,
    SearchConfig,
    canonical_orbit_key,
    evaluate_profile,
    feasible,
    finite,
    normalize_probability,
    profile_metrics,
    validate_problem,
)


def candidate_profiles(
    problem: Problem, config: SearchConfig
) -> Iterable[tuple[str, np.ndarray, str, dict[str, Any] | None]]:
    mode_count = len(problem.modes)
    yield (
        "uniform",
        np.full(mode_count, 1.0 / mode_count, dtype=np.float64),
        "deterministic",
        None,
    )
    for triad_index, triad in enumerate(problem.triads):
        p = np.zeros(mode_count, dtype=np.float64)
        p[[triad.left, triad.right, triad.out]] = 1.0 / 3.0
        yield f"triad-seed-{triad_index}", p, "deterministic", None
    for profile_index, profile in enumerate(problem.profiles):
        profile_id = str(profile.get("profile_id", f"input-{profile_index}"))
        metadata = {
            key: profile[key]
            for key in ("trajectory_id", "time", "duration", "cutoff")
            if key in profile
        }
        yield (
            profile_id,
            normalize_probability(profile["probability"], config.zero_eps),
            "input",
            metadata,
        )
    concentrations = (0.03, 0.08, 0.2, 0.5, 1.0, 2.0)
    for seed in config.seeds:
        rng = np.random.default_rng(seed)
        for sample_index in range(max(0, config.random_samples)):
            alpha = concentrations[sample_index % len(concentrations)]
            p = rng.dirichlet(np.full(mode_count, alpha, dtype=np.float64))
            yield f"seed{seed}-dirichlet-{sample_index}", p, "random", None


def local_improve(
    problem: Problem,
    start: np.ndarray,
    config: SearchConfig,
    seed: int,
) -> np.ndarray:
    rng = np.random.default_rng(seed)
    current = normalize_probability(start, config.zero_eps)
    if len(current) < 2:
        return current
    current_metrics = profile_metrics(problem, current, config.zero_eps)
    current_gamma = current_metrics["gamma"]
    current_score = -math.inf if current_gamma is None else float(current_gamma)
    for _ in range(max(0, config.local_steps)):
        proposal = current.copy()
        donor = int(rng.integers(0, len(proposal)))
        receiver = int(rng.integers(0, len(proposal) - 1))
        if receiver >= donor:
            receiver += 1
        transfer = float(rng.uniform(0.0, 0.5)) * proposal[donor]
        proposal[donor] -= transfer
        proposal[receiver] += transfer
        metrics = profile_metrics(problem, proposal, config.zero_eps)
        if not feasible(metrics, config.constraints):
            continue
        proposal_gamma = metrics["gamma"]
        score = -math.inf if proposal_gamma is None else float(proposal_gamma)
        if score > current_score:
            current = proposal
            current_score = score
    return current


def window_rows(
    rows: list[dict[str, Any]],
    window_sizes: tuple[int, ...],
    target_eta: float,
) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, Any], list[dict[str, Any]]] = {}
    for row in rows:
        trajectory = str(row.get("trajectory_id", "default"))
        cutoff = row.get("cutoff")
        grouped.setdefault((trajectory, cutoff), []).append(row)
    windows: list[dict[str, Any]] = []
    for (trajectory, cutoff), group in grouped.items():
        group.sort(key=lambda row: (float(row.get("time", 0.0)), str(row["profile_id"])))
        sizes = set(window_sizes)
        sizes.add(len(group))
        for size in sorted(value for value in sizes if 0 < value <= len(group)):
            for start in range(0, len(group) - size + 1):
                segment = group[start : start + size]
                durations = np.asarray(
                    [finite(row.get("duration", 1.0), "duration") for row in segment],
                    dtype=np.float64,
                )
                gammas = np.asarray(
                    [float(row["gamma"]) for row in segment if row.get("gamma") is not None],
                    dtype=np.float64,
                )
                if len(gammas) != len(segment) or np.any(durations <= 0.0):
                    continue
                length = float(np.sum(durations))
                integral = float(durations @ gammas)
                average = float(integral / length)
                windows.append(
                    {
                        "trajectory_id": trajectory,
                        "cutoff": cutoff,
                        "window_size": size,
                        "start_profile_id": segment[0]["profile_id"],
                        "end_profile_id": segment[-1]["profile_id"],
                        "interval_length": length,
                        "integrated_gamma": integral,
                        "average_gamma": average,
                        "observed_eta_margin": float(1.0 - average),
                        "target_counterexample": bool(average > 1.0 - target_eta),
                    }
                )
    return windows


def audit_problem(problem: Problem, config: SearchConfig) -> dict[str, Any]:
    validate_problem(problem, config.zero_eps)
    rows: list[dict[str, Any]] = []
    seen: set[bytes] = set()
    for profile_id, probability, source, metadata in candidate_profiles(problem, config):
        normalized = normalize_probability(probability, config.zero_eps)
        key = np.round(normalized, 14).tobytes()
        # Preserve every trajectory sample even when two times carry the same
        # probability vector.  Deduplication is only for generated search rows;
        # dropping repeated input states would corrupt duration-weighted windows.
        if source != "input":
            if key in seen:
                continue
            seen.add(key)
        rows.append(
            evaluate_profile(
                problem,
                normalized,
                config,
                profile_id=profile_id,
                source=source,
                extra=metadata,
            )
        )

    feasible_rows = [
        row
        for row in rows
        if row["concentration_constraints_satisfied"] and row.get("gamma") is not None
    ]
    starts = sorted(feasible_rows, key=lambda row: float(row["gamma"]), reverse=True)[:8]
    for local_index, start in enumerate(starts):
        probability = local_improve(
            problem,
            np.asarray(start["probability"], dtype=np.float64),
            config,
            seed=10_000 + local_index,
        )
        rows.append(
            evaluate_profile(
                problem,
                probability,
                config,
                profile_id=f"local-improvement-{local_index}",
                source="local-search",
                extra={"parent_profile_id": start["profile_id"]},
            )
        )

    feasible_rows = [
        row
        for row in rows
        if row["concentration_constraints_satisfied"] and row.get("gamma") is not None
    ]
    worst = max(feasible_rows, key=lambda row: float(row["gamma"]), default=None)
    input_rows = [row for row in rows if row["source"] == "input"]
    windows = window_rows(input_rows, config.window_sizes, config.target_eta)
    worst_window = max(windows, key=lambda row: float(row["average_gamma"]), default=None)
    target_counterexamples = [
        row for row in feasible_rows if row["branch"] == "target-counterexample"
    ]
    max_identity_residual = max(
        (
            float(row["identity_residual"])
            for row in rows
            if row.get("identity_residual") is not None
        ),
        default=0.0,
    )
    return {
        "problem_id": problem.problem_id,
        "coefficient_semantics": problem.coefficient_semantics,
        "convention": problem.convention,
        "mode_count": len(problem.modes),
        "triad_count": len(problem.triads),
        "orbit_count": len(
            {canonical_orbit_key(problem, triad) for triad in problem.triads}
        ),
        "candidate_count": len(rows),
        "feasible_candidate_count": len(feasible_rows),
        "target_counterexample_count": len(target_counterexamples),
        "no_counterexample_sampled": len(target_counterexamples) == 0,
        "worst_profile": worst,
        "observed_pointwise_eta_margin": (
            None if worst is None else float(1.0 - float(worst["gamma"]))
        ),
        "worst_window": worst_window,
        "window_count": len(windows),
        "window_target_counterexample_count": sum(
            1 for row in windows if row["target_counterexample"]
        ),
        "input_profile_rows": input_rows,
        "max_finite_identity_residual": max_identity_residual,
        "profile_samples": sorted(
            feasible_rows, key=lambda row: float(row["gamma"]), reverse=True
        )[:25],
    }
