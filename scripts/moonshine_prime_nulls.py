#!/usr/bin/env python3
"""Schema-level null-model harness for the moonshine-primes program."""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable

from moonshine_prime_object import SSP_PRIMES, observe, parse_state

TARGET_PRIMES = (47, 59, 71)


@dataclass(frozen=True)
class NullResult:
    name: str
    observed_score: float
    null_mean: float
    null_max: float
    p_value: float
    passes_null: bool


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="Path to a MoonshinePrimeState JSON file")
    parser.add_argument("--samples", type=int, default=500)
    parser.add_argument("--alpha", type=float, default=0.05)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--output", help="Optional path for JSON results")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def target_prime_score(signature: dict[int, bool], factor_vector: dict[int, int]) -> float:
    weighted = sum(factor_vector[p] for p in TARGET_PRIMES)
    signature_hits = sum(1 for p in TARGET_PRIMES if signature[p])
    support_total = sum(max(v, 0) for v in factor_vector.values()) or 1
    return (weighted / support_total) + (signature_hits / len(TARGET_PRIMES))


def empirical_p_value(observed: float, samples: list[float]) -> float:
    extreme = sum(1 for value in samples if value >= observed)
    return (extreme + 1) / (len(samples) + 1)


def run_null(
    name: str,
    observed_score: float,
    sampler: Callable[[], float],
    samples: int,
    alpha: float,
) -> NullResult:
    values = [sampler() for _ in range(samples)]
    p_value = empirical_p_value(observed_score, values)
    return NullResult(
        name=name,
        observed_score=observed_score,
        null_mean=sum(values) / len(values),
        null_max=max(values),
        p_value=p_value,
        passes_null=p_value >= alpha,
    )


def main() -> int:
    args = parse_args()
    rng = random.Random(args.seed)

    payload = json.loads(Path(args.input).read_text())
    state = parse_state(payload)
    observed = observe(state)
    observed_score = target_prime_score(observed.signature, observed.factor_vector)

    factor_values = [state.factor_vector[p] for p in SSP_PRIMES]
    signature_values = [state.signature[p] for p in SSP_PRIMES]
    carrier_abs = [abs(v) for v in state.carrier]
    carrier_len = len(state.carrier)
    support_count = len(observed.factor_support)
    support_weight = observed.factor_support_weight

    def random_partition_score() -> float:
        permuted_values = factor_values[:]
        rng.shuffle(permuted_values)
        permuted_factors = dict(zip(SSP_PRIMES, permuted_values))
        permuted_signature = {
            p: permuted_factors[p] > 0 or signature_values[i]
            for i, p in enumerate(SSP_PRIMES)
        }
        return target_prime_score(permuted_signature, permuted_factors)

    def random_ternary_score() -> float:
        carrier = [rng.choice([-1, 0, 1]) for _ in range(carrier_len)]
        target_mass = sum(abs(v) for v in carrier[: min(3, carrier_len)])
        total_mass = sum(abs(v) for v in carrier) or 1
        target_hits = sum(1 for v in carrier[: min(3, carrier_len)] if v != 0)
        return (target_mass / total_mass) + (target_hits / max(1, min(3, carrier_len)))

    def matched_support_score() -> float:
        support = set(rng.sample(SSP_PRIMES, support_count))
        weights = rng.sample(factor_values, len(factor_values))
        factors = {p: 0 for p in SSP_PRIMES}
        for p, w in zip(SSP_PRIMES, weights):
            if p in support:
                factors[p] = w
        total = sum(factors.values())
        if total == 0 and support:
            chosen = next(iter(support))
            factors[chosen] = max(1, support_weight)
        signature = {p: factors[p] > 0 for p in SSP_PRIMES}
        return target_prime_score(signature, factors)

    def randomized_rotation_score() -> float:
        rotated = carrier_abs[:]
        rng.shuffle(rotated)
        target_mass = sum(rotated[: min(3, carrier_len)])
        total_mass = sum(rotated) or 1
        entropy_proxy = sum(1 for v in rotated if v > 0) / max(1, carrier_len)
        return (target_mass / total_mass) + entropy_proxy / 2.0

    results = [
        run_null("random_partition", observed_score, random_partition_score, args.samples, args.alpha),
        run_null("random_ternary_state", observed_score, random_ternary_score, args.samples, args.alpha),
        run_null("matched_support_control", observed_score, matched_support_score, args.samples, args.alpha),
        run_null("randomized_rotation_control", observed_score, randomized_rotation_score, args.samples, args.alpha),
    ]

    output = {
        "target_primes": list(TARGET_PRIMES),
        "observed_score": observed_score,
        "alpha": args.alpha,
        "samples": args.samples,
        "seed": args.seed,
        "results": [asdict(r) for r in results],
        "stop_bridge_program": any(r.passes_null for r in results),
        "stop_reason": (
            "at least one null reproduces the observed target-prime score above the alpha threshold"
            if any(r.passes_null for r in results)
            else "all schema-level nulls remain below the stop threshold"
        ),
    }

    text = json.dumps(output, indent=2 if args.pretty else None, sort_keys=True)
    if args.output:
        Path(args.output).write_text(text + ("\n" if args.pretty else ""))
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
