#!/usr/bin/env python3
"""Abel triadic stationarity proxy harness.

This pure-stdlib local diagnostic synthesizes finite shell/triadic measures,
normalizes them into a bounded Abel-mass proxy, pushes the proxy through a
deterministic transfer rule, and reports the resulting stationarity defect

    delta = ||T_* mu - mu||_1

against shell, triad-type, and kappa-observable marginals.  The kappa-bias
bound reported here is the requested proxy quantity

    delta * sqrt(11/60).

It is a finite synthetic harness only.  It does not construct a PDE measure
and it always emits promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


EPS = 1.0e-12
KAPPA_BIAS_CONSTANT = math.sqrt(11.0 / 60.0)


@dataclass(frozen=True)
class ShellAtom:
    shell: int
    depth: int
    energy: float
    mass: float


@dataclass(frozen=True)
class TriadicAtom:
    shell: int
    depth: int
    triad_type: str
    kappa: float
    lambda_weight: float
    raw_weight: float
    mass: float


@dataclass(frozen=True)
class MeasureSummary:
    atoms: int
    total_mass: float
    min_mass: float | None
    max_mass: float | None
    mean_shell: float | None
    mean_kappa: float | None
    mean_kappa_sq: float | None
    mean_lambda: float | None
    mean_bias_observable: float | None
    weighted_kappa_bias: float | None


@dataclass(frozen=True)
class StationarityDefect:
    delta_shell_l1: float
    delta_triad_type_l1: float
    delta_kappa_bin_l1: float
    delta_moment_l1: float
    delta: float
    kappa_bias_bound: float
    kappa_bias_constant: float


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=4096, help="Number of synthetic triadic atoms.")
    parser.add_argument("--shells", type=int, default=9, help="Number of dyadic shells.")
    parser.add_argument("--abel-rho", type=float, default=0.82, help="Abel rho in [0,1).")
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--bins", type=int, default=24, help="Kappa histogram bins.")
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.shells <= 0:
        raise ValueError("--shells must be positive")
    if not (0.0 <= args.abel_rho < 1.0):
        raise ValueError("--abel-rho must satisfy 0 <= rho < 1")
    if args.bins <= 1:
        raise ValueError("--bins must be greater than 1")


def abel_shell_weights(shells: int, rho: float) -> list[float]:
    weights = [(1.0 - rho) * (rho**depth) for depth in range(shells)]
    total = sum(weights)
    if total <= EPS:
        raise ValueError("degenerate Abel shell weights")
    return [weight / total for weight in weights]


def choose_index(rng: random.Random, weights: Sequence[float]) -> int:
    threshold = rng.random() * sum(weights)
    running = 0.0
    for index, weight in enumerate(weights):
        running += weight
        if running >= threshold:
            return index
    return len(weights) - 1


def synthesize_shell_measure(shells: int, rho: float) -> list[ShellAtom]:
    weights = abel_shell_weights(shells, rho)
    atoms: list[ShellAtom] = []
    for depth, mass in enumerate(weights):
        shell = 1 << depth
        energy = mass / math.sqrt(float(shell))
        atoms.append(ShellAtom(shell=shell, depth=depth, energy=energy, mass=mass))
    return atoms


def triad_type_for_depth(depth: int, rng: random.Random) -> str:
    roll = rng.random()
    if roll < 0.45:
        return "local"
    if roll < 0.75:
        return "high_high_to_low" if depth > 0 else "local"
    return "high_low_to_high"


def sample_kappa(triad_type: str, rng: random.Random) -> float:
    theta = rng.uniform(0.0, 2.0 * math.pi)
    base = math.cos(theta)
    if triad_type == "local":
        return base
    if triad_type == "high_high_to_low":
        return max(-1.0, min(1.0, 0.82 * base + 0.18 * math.cos(3.0 * theta)))
    if triad_type == "high_low_to_high":
        return max(-1.0, min(1.0, 0.70 * base - 0.20 * math.sin(2.0 * theta)))
    raise ValueError(f"unknown triad type: {triad_type}")


def lambda_weight(shell: int, triad_type: str, kappa: float) -> float:
    shell_factor = 1.0 + 0.08 * math.log2(float(shell))
    type_factor = {
        "local": 1.00,
        "high_high_to_low": 0.92,
        "high_low_to_high": 1.08,
    }[triad_type]
    angular_factor = 1.0 + 0.12 * (kappa * kappa - 0.5)
    return max(EPS, shell_factor * type_factor * angular_factor)


def normalize_triad_atoms(atoms: Sequence[TriadicAtom]) -> list[TriadicAtom]:
    total = sum(atom.raw_weight for atom in atoms)
    if total <= EPS:
        raise ValueError("cannot normalize zero triadic mass")
    return [
        TriadicAtom(
            shell=atom.shell,
            depth=atom.depth,
            triad_type=atom.triad_type,
            kappa=atom.kappa,
            lambda_weight=atom.lambda_weight,
            raw_weight=atom.raw_weight,
            mass=atom.raw_weight / total,
        )
        for atom in atoms
    ]


def synthesize_triadic_measure(samples: int, shells: int, rho: float, seed: int) -> list[TriadicAtom]:
    rng = random.Random(seed)
    shell_weights = abel_shell_weights(shells, rho)
    atoms: list[TriadicAtom] = []
    for _ in range(samples):
        depth = choose_index(rng, shell_weights)
        shell = 1 << depth
        triad_type = triad_type_for_depth(depth, rng)
        kappa = sample_kappa(triad_type, rng)
        lam = lambda_weight(shell, triad_type, kappa)
        raw_weight = shell_weights[depth] * lam
        atoms.append(
            TriadicAtom(
                shell=shell,
                depth=depth,
                triad_type=triad_type,
                kappa=kappa,
                lambda_weight=lam,
                raw_weight=raw_weight,
                mass=0.0,
            )
        )
    return normalize_triad_atoms(atoms)


def transfer_atom(atom: TriadicAtom) -> TriadicAtom:
    if atom.triad_type == "local":
        next_type = "high_low_to_high"
        next_depth = min(atom.depth + 1, 30)
        next_kappa = max(-1.0, min(1.0, 0.86 * atom.kappa + 0.10))
    elif atom.triad_type == "high_low_to_high":
        next_type = "local"
        next_depth = atom.depth
        next_kappa = max(-1.0, min(1.0, -0.72 * atom.kappa))
    else:
        next_type = "local"
        next_depth = max(0, atom.depth - 1)
        next_kappa = max(-1.0, min(1.0, 0.64 * atom.kappa - 0.08))
    next_shell = 1 << min(next_depth, 30)
    lam = lambda_weight(next_shell, next_type, next_kappa)
    return TriadicAtom(
        shell=next_shell,
        depth=next_depth,
        triad_type=next_type,
        kappa=next_kappa,
        lambda_weight=lam,
        raw_weight=atom.mass,
        mass=atom.mass,
    )


def pushforward_measure(atoms: Sequence[TriadicAtom]) -> list[TriadicAtom]:
    return list(normalize_triad_atoms([transfer_atom(atom) for atom in atoms]))


def weighted_sum(atoms: Sequence[TriadicAtom], fn: Callable[[TriadicAtom], float]) -> float:
    return sum(atom.mass * fn(atom) for atom in atoms)


def summarize_measure(atoms: Sequence[TriadicAtom]) -> MeasureSummary:
    if not atoms:
        return MeasureSummary(0, 0.0, None, None, None, None, None, None, None, None)
    total_mass = sum(atom.mass for atom in atoms)
    if total_mass <= EPS:
        raise ValueError("measure has nonpositive total mass")
    return MeasureSummary(
        atoms=len(atoms),
        total_mass=total_mass,
        min_mass=min(atom.mass for atom in atoms),
        max_mass=max(atom.mass for atom in atoms),
        mean_shell=weighted_sum(atoms, lambda atom: float(atom.shell)),
        mean_kappa=weighted_sum(atoms, lambda atom: atom.kappa),
        mean_kappa_sq=weighted_sum(atoms, lambda atom: atom.kappa * atom.kappa),
        mean_lambda=weighted_sum(atoms, lambda atom: atom.lambda_weight),
        mean_bias_observable=weighted_sum(atoms, lambda atom: atom.kappa * atom.kappa - 0.5),
        weighted_kappa_bias=weighted_sum(atoms, lambda atom: atom.lambda_weight * (atom.kappa * atom.kappa - 0.5)),
    )


def categorical_distribution(atoms: Sequence[TriadicAtom], fn: Callable[[TriadicAtom], str]) -> dict[str, float]:
    out: dict[str, float] = {}
    for atom in atoms:
        key = fn(atom)
        out[key] = out.get(key, 0.0) + atom.mass
    return out


def l1_dict(a: dict[str, float], b: dict[str, float]) -> float:
    keys = set(a) | set(b)
    return sum(abs(a.get(key, 0.0) - b.get(key, 0.0)) for key in keys)


def kappa_histogram(atoms: Sequence[TriadicAtom], bins: int) -> dict[str, float]:
    out = {str(index): 0.0 for index in range(bins)}
    for atom in atoms:
        index = int((max(-1.0, min(1.0, atom.kappa)) + 1.0) * 0.5 * bins)
        index = max(0, min(bins - 1, index))
        out[str(index)] += atom.mass
    return out


def stationarity_defect(source: Sequence[TriadicAtom], pushed: Sequence[TriadicAtom], bins: int) -> StationarityDefect:
    source_summary = summarize_measure(source)
    pushed_summary = summarize_measure(pushed)
    moment_pairs = [
        (source_summary.mean_kappa, pushed_summary.mean_kappa),
        (source_summary.mean_kappa_sq, pushed_summary.mean_kappa_sq),
        (source_summary.mean_lambda, pushed_summary.mean_lambda),
        (source_summary.weighted_kappa_bias, pushed_summary.weighted_kappa_bias),
    ]
    delta_moment_l1 = sum(abs(float(a) - float(b)) for a, b in moment_pairs if a is not None and b is not None)
    delta_shell_l1 = l1_dict(
        categorical_distribution(source, lambda atom: str(atom.shell)),
        categorical_distribution(pushed, lambda atom: str(atom.shell)),
    )
    delta_triad_type_l1 = l1_dict(
        categorical_distribution(source, lambda atom: atom.triad_type),
        categorical_distribution(pushed, lambda atom: atom.triad_type),
    )
    delta_kappa_bin_l1 = l1_dict(kappa_histogram(source, bins), kappa_histogram(pushed, bins))
    delta = max(delta_shell_l1, delta_triad_type_l1, delta_kappa_bin_l1, delta_moment_l1)
    return StationarityDefect(
        delta_shell_l1=delta_shell_l1,
        delta_triad_type_l1=delta_triad_type_l1,
        delta_kappa_bin_l1=delta_kappa_bin_l1,
        delta_moment_l1=delta_moment_l1,
        delta=delta,
        kappa_bias_bound=delta * KAPPA_BIAS_CONSTANT,
        kappa_bias_constant=KAPPA_BIAS_CONSTANT,
    )


def quantiles(values: Sequence[float]) -> dict[str, float]:
    if not values:
        return {}
    ordered = sorted(values)

    def q(probability: float) -> float:
        if len(ordered) == 1:
            return ordered[0]
        position = probability * (len(ordered) - 1)
        lo = int(math.floor(position))
        hi = int(math.ceil(position))
        if lo == hi:
            return ordered[lo]
        mix = position - lo
        return ordered[lo] * (1.0 - mix) + ordered[hi] * mix

    return {"q05": q(0.05), "q50": q(0.50), "q95": q(0.95)}


def run(samples: int, shells: int, abel_rho: float, seed: int, bins: int) -> dict[str, object]:
    shell_measure = synthesize_shell_measure(shells=shells, rho=abel_rho)
    source = synthesize_triadic_measure(samples=samples, shells=shells, rho=abel_rho, seed=seed)
    pushed = pushforward_measure(source)
    defect = stationarity_defect(source, pushed, bins)
    checks = {
        "bounded_shell_mass": abs(sum(atom.mass for atom in shell_measure) - 1.0) < 1.0e-10,
        "bounded_triadic_mass": abs(sum(atom.mass for atom in source) - 1.0) < 1.0e-10,
        "bounded_pushforward_mass": abs(sum(atom.mass for atom in pushed) - 1.0) < 1.0e-10,
        "finite_delta": math.isfinite(defect.delta) and defect.delta >= 0.0,
        "kappa_bias_bound_matches_delta_sqrt_11_60": abs(defect.kappa_bias_bound - defect.delta * KAPPA_BIAS_CONSTANT) < 1.0e-12,
        "promotion_false": True,
    }
    return {
        "ok": all(checks.values()),
        "script": "scripts/ns_abel_triadic_stationarity_proxy_harness.py",
        "seed": seed,
        "samples": samples,
        "shells": shells,
        "abel_rho": abel_rho,
        "bins": bins,
        "scope": "finite_synthetic_shell_triadic_stationarity_proxy_not_pde_measure",
        "bounded_mass_proxy": {
            "shell_total_mass": sum(atom.mass for atom in shell_measure),
            "triadic_total_mass": sum(atom.mass for atom in source),
            "pushforward_total_mass": sum(atom.mass for atom in pushed),
            "shell_energy_total": sum(atom.energy for atom in shell_measure),
        },
        "shell_measure": [asdict(atom) for atom in shell_measure],
        "source_summary": asdict(summarize_measure(source)),
        "pushforward_summary": asdict(summarize_measure(pushed)),
        "stationarity_defect": asdict(defect),
        "kappa_bias_bound_formula": "delta * sqrt(11/60)",
        "diagnostics": {
            "source_kappa_quantiles": quantiles([atom.kappa for atom in source]),
            "pushforward_kappa_quantiles": quantiles([atom.kappa for atom in pushed]),
            "triad_type_distribution": categorical_distribution(source, lambda atom: atom.triad_type),
            "pushforward_triad_type_distribution": categorical_distribution(pushed, lambda atom: atom.triad_type),
        },
        "checks": checks,
        "promotion": False,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    payload = run(
        samples=args.samples,
        shells=args.shells,
        abel_rho=args.abel_rho,
        seed=args.seed,
        bins=args.bins,
    )
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
