#!/usr/bin/env python3
"""Verify the finite NS S2 stretching formula.

This harness samples triads (a,b), forms c = normalize(a+b), uses the local
S2 Biot-Savart/curl eigenbundle provider, and checks the finite-symbol law

    stretching = lambda(c) * (2*kappa^2 - 1).

Here kappa is the component of the tangent output direction Y/|Y| along
omega_hat(c), with Y taken as P_c b for this local triad diagnostic.  The
output vorticity direction is Omega_c = normalize(c x Y), and stretching is
computed from the traceless two-eigenvalue strain model:

    S e_plus = +lambda e_plus,   S omega_hat = -lambda omega_hat.

This is a finite-dimensional diagnostic only; it is not a PDE theorem or Clay
promotion.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType
from typing import Sequence


SCRIPT_DIR = Path(__file__).resolve().parent
PROVIDER_PATH = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"
EPS = 1.0e-12
DEFAULT_BINS = (
    (0.0, 0.1),
    (0.1, 0.2),
    (0.2, 0.3),
    (0.3, 0.4),
    (0.4, 0.5),
    (0.5, 0.6),
    (0.6, 1.0 / math.sqrt(2.0)),
    (1.0 / math.sqrt(2.0), 0.8),
    (0.8, 0.9),
    (0.9, 1.0 + 1.0e-12),
)


Vec3 = tuple[float, float, float]


@dataclass
class BinStats:
    low: float
    high: float
    count: int = 0
    mean_stretching: float = 0.0
    min_stretching: float | None = None
    max_stretching: float | None = None
    negative_fraction: float = 0.0
    positive_fraction: float = 0.0
    zero_fraction: float = 0.0


@dataclass
class Accumulator:
    count: int = 0
    total_stretching: float = 0.0
    negative: int = 0
    positive: int = 0
    zero: int = 0
    min_stretching: float | None = None
    max_stretching: float | None = None

    def add(self, value: float) -> None:
        self.count += 1
        self.total_stretching += value
        if value < -1.0e-12:
            self.negative += 1
        elif value > 1.0e-12:
            self.positive += 1
        else:
            self.zero += 1
        self.min_stretching = value if self.min_stretching is None else min(self.min_stretching, value)
        self.max_stretching = value if self.max_stretching is None else max(self.max_stretching, value)

    def finalize(self, low: float, high: float) -> BinStats:
        if self.count == 0:
            return BinStats(low=low, high=high)
        return BinStats(
            low=low,
            high=high,
            count=self.count,
            mean_stretching=self.total_stretching / self.count,
            min_stretching=self.min_stretching,
            max_stretching=self.max_stretching,
            negative_fraction=self.negative / self.count,
            positive_fraction=self.positive / self.count,
            zero_fraction=self.zero / self.count,
        )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument("--json-output", type=Path, help="write compact JSON payload to this path")
    return parser.parse_args(argv)


def load_provider() -> ModuleType:
    if not PROVIDER_PATH.exists():
        raise FileNotFoundError(f"missing provider: {PROVIDER_PATH}")
    spec = importlib.util.spec_from_file_location("ns_s2_biot_savart_eigenbundle", PROVIDER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load provider spec: {PROVIDER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def bin_index(abs_kappa: float) -> int:
    for idx, (low, high) in enumerate(DEFAULT_BINS):
        if low <= abs_kappa < high:
            return idx
    return len(DEFAULT_BINS) - 1


def run(samples: int, seed: int) -> dict[str, object]:
    provider = load_provider()
    rng = random.Random(seed)
    bins = [Accumulator() for _ in DEFAULT_BINS]

    accepted = 0
    degenerates = 0
    max_abs_error = 0.0
    max_orthogonality_error = 0.0
    max_kappa_abs = 0.0
    lambda_sum = 0.0
    lambda_sq_sum = 0.0
    stretching_sum = 0.0
    formula_sum = 0.0
    negative = 0
    positive = 0
    zero = 0

    attempts = 0
    max_attempts = max(samples * 20, samples + 100)
    while accepted < samples and attempts < max_attempts:
        attempts += 1
        a = random_unit(rng)
        b = random_unit(rng)
        c = provider.normalize(provider.add(a, b), EPS)
        if c is None:
            degenerates += 1
            continue
        bundle = provider.angular_eigenbundle(c, EPS)
        y = provider.project(c, b, EPS)
        if bundle is None or y is None:
            degenerates += 1
            continue
        y_hat = provider.normalize(y, EPS)
        if y_hat is None:
            degenerates += 1
            continue
        omega_out = provider.normalize(provider.cross(c, y_hat), EPS)
        if omega_out is None:
            degenerates += 1
            continue

        lam = math.hypot(bundle.m11, bundle.m12)
        kappa = provider.dot(y_hat, bundle.omega_hat)
        stretching = lam * (
            provider.dot(omega_out, bundle.e_plus) ** 2
            - provider.dot(omega_out, bundle.omega_hat) ** 2
        )
        formula = lam * (2.0 * kappa * kappa - 1.0)
        err = abs(stretching - formula)
        max_abs_error = max(max_abs_error, err)
        max_orthogonality_error = max(
            max_orthogonality_error,
            abs(provider.dot(c, bundle.e_plus)),
            abs(provider.dot(c, bundle.omega_hat)),
            abs(provider.dot(bundle.e_plus, bundle.omega_hat)),
            abs(provider.dot(c, omega_out)),
        )
        max_kappa_abs = max(max_kappa_abs, abs(kappa))

        accepted += 1
        lambda_sum += lam
        lambda_sq_sum += lam * lam
        stretching_sum += stretching
        formula_sum += formula
        if stretching < -1.0e-12:
            negative += 1
        elif stretching > 1.0e-12:
            positive += 1
        else:
            zero += 1
        bins[bin_index(abs(kappa))].add(stretching)

    if accepted < samples:
        raise RuntimeError(f"only accepted {accepted}/{samples} samples after {attempts} attempts")

    bin_stats = [
        bins[idx].finalize(DEFAULT_BINS[idx][0], DEFAULT_BINS[idx][1])
        for idx in range(len(DEFAULT_BINS))
    ]
    return {
        "harness": "ns_stretching_formula_harness",
        "script": "scripts/ns_stretching_formula_harness.py",
        "theorem_label": "NS-F2",
        "theorem_name": "NSCoherentStretchingExactFormula",
        "scope": "finite_symbol_diagnostic_not_pde_proof",
        "provider": str(PROVIDER_PATH),
        "seed": seed,
        "requested_samples": samples,
        "accepted_samples": accepted,
        "degenerate_attempts": degenerates,
        "attempts": attempts,
        "max_abs_error": max_abs_error,
        "max_orthogonality_error": max_orthogonality_error,
        "max_abs_kappa": max_kappa_abs,
        "mean_lambda": lambda_sum / accepted,
        "mean_lambda_sq": lambda_sq_sum / accepted,
        "mean_stretching": stretching_sum / accepted,
        "mean_formula": formula_sum / accepted,
        "exact_formula": "Omega_c dot S(c) Omega_c = lambda(c)*(2*kappa^2-1)",
        "exact_constants": {
            "zero_crossing_abs_kappa": 1.0 / math.sqrt(2.0),
            "compressive_region": "|kappa| < 1/sqrt(2)",
            "stretching_region": "|kappa| > 1/sqrt(2)",
        },
        "negative_fraction": negative / accepted,
        "positive_fraction": positive / accepted,
        "zero_fraction": zero / accepted,
        "threshold_prediction": "stretching changes sign at |kappa| = 1/sqrt(2)",
        "sign_bins": [asdict(item) for item in bin_stats],
        "promotion": {
            "finite_formula_checked": max_abs_error <= 1.0e-10,
            "pde_promotion": False,
            "clay_promotion": False,
        },
        "promotion_false": True,
        "clay_promotion": False,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    result = run(args.samples, args.seed)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        with args.json_output.open("w", encoding="utf-8") as handle:
            json.dump(result, handle, sort_keys=True, separators=(",", ":"))
            handle.write("\n")
    if args.json:
        print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
