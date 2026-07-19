#!/usr/bin/env python3
"""Fail-closed 15SSP factor-fibre admissibility benchmark.

This is an evaluation harness, not a factoring algorithm. It tests whether
public 15SSP residue features distinguish the true factors of an unbiased toy
semiprime from independently sampled same-size prime nonfactors.

The hidden factors are used only as evaluation labels when computing AUC. They
are never exposed to a score, candidate order, or search procedure.

Admission rules
---------------
* No trial division or candidate enumeration.
* No ordering by distance from sqrt(n).
* No Pollard rho, ECM, GNFS, or factor oracle in scoring.
* SSP15 is compared with fixed non-SSP and random-prime controls.
* Intentionally SSP-constrained prime generation is a separate positive
  control and can establish only structured-source detection.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import random
import statistics
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

SSP15: tuple[int, ...] = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71
)
NON_SSP15: tuple[int, ...] = (
    37, 43, 53, 61, 67, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113
)
STRUCTURED_MODULI: tuple[int, ...] = (3, 5, 7, 11)
MILLER_RABIN_BASES: tuple[int, ...] = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
)

# Machine-readable declaration consumed by tests and receipts. The harness has
# no factor-search lane at all; true factors are evaluation labels only.
SEARCH_METHODS_USED: tuple[str, ...] = ()
FORBIDDEN_SEARCH_METHODS: tuple[str, ...] = (
    "trial-division",
    "sqrt-window-ordering",
    "pollard-rho",
    "ecm",
    "gnfs",
    "private-factor-oracle-in-scoring",
)


def is_probable_prime(n: int) -> bool:
    """Deterministic enough for the bounded toy inputs used by this harness."""
    if n < 2:
        return False
    for p in MILLER_RABIN_BASES:
        if n % p == 0:
            return n == p

    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2

    for a in MILLER_RABIN_BASES:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def random_prime(
    bits: int,
    rng: random.Random,
    residue_constraints: dict[int, int] | None = None,
) -> int:
    """Sample a probable prime; constraints are used only for positive control."""
    if bits < 4:
        raise ValueError("prime bit length must be at least 4")
    if bits > 96:
        raise ValueError("toy benchmark limits each factor to at most 96 bits")

    constraints = residue_constraints or {}
    lo = 1 << (bits - 1)
    hi = (1 << bits) - 1

    if constraints:
        combined_modulus = math.prod(constraints)
        combined_residue = 0
        for modulus, residue in constraints.items():
            partial = combined_modulus // modulus
            combined_residue += residue * partial * pow(partial, -1, modulus)
        combined_residue %= combined_modulus
        k_min = (lo - combined_residue + combined_modulus - 1) // combined_modulus
        k_max = (hi - combined_residue) // combined_modulus
        if k_min > k_max:
            raise RuntimeError("no constrained values exist at this bit length")
        for _ in range(200_000):
            k = rng.randrange(k_min, k_max + 1)
            candidate = combined_residue + k * combined_modulus
            if candidate % 2 == 0:
                continue
            if is_probable_prime(candidate):
                return candidate
    else:
        for _ in range(200_000):
            candidate = rng.randrange(lo, hi + 1) | lo | 1
            if is_probable_prime(candidate):
                return candidate
    raise RuntimeError("prime generation failed; constraints may be too tight")


def sample_semiprime(
    bits: int,
    rng: random.Random,
    *,
    structured_source: bool,
) -> tuple[int, int, int]:
    """Return n and its two evaluation labels; no search recovers them."""
    left_bits = bits // 2
    right_bits = bits - left_bits
    constraints = (
        {modulus: 1 for modulus in STRUCTURED_MODULI}
        if structured_source
        else None
    )
    p = random_prime(left_bits, rng, constraints)
    q = random_prime(right_bits, rng, constraints)
    while q == p:
        q = random_prime(right_bits, rng, constraints)
    return p * q, min(p, q), max(p, q)


def random_control_basis(rng: random.Random, size: int = 15) -> tuple[int, ...]:
    pool = tuple(
        candidate
        for candidate in range(3, 500)
        if is_probable_prime(candidate) and candidate not in SSP15
    )
    return tuple(rng.sample(pool, size))


def basis_hash(basis: Sequence[int]) -> str:
    text = ",".join(map(str, basis)).encode("ascii")
    return hashlib.sha256(text).hexdigest()[:12]


def product_pair_ambiguity_log2(n: int, basis: Sequence[int]) -> float:
    """Residue-pair ambiguity; this is not a factor-recovery calculation."""
    ambiguity = 0.0
    for modulus in basis:
        residue = n % modulus
        # For prime modulus r: r-1 unit pairs solve ab=residue when residue != 0.
        # If residue == 0 there are 2r-1 pairs with at least one zero component.
        pair_count = 2 * modulus - 1 if residue == 0 else modulus - 1
        ambiguity += math.log2(pair_count)
    return ambiguity


def low_defect_score(candidate: int, basis: Sequence[int]) -> float:
    """Public candidate-only feature: fraction of residues equal to ±1."""
    return sum(
        candidate % modulus in (1, modulus - 1)
        for modulus in basis
    ) / len(basis)


def structured_source_score(candidate: int, basis: Sequence[int]) -> float:
    """Positive-control feature for the deliberately constrained generator."""
    tested = tuple(modulus for modulus in STRUCTURED_MODULI if modulus in basis)
    if not tested:
        return 0.0
    return sum(candidate % modulus == 1 for modulus in tested) / len(tested)


def product_compatible_score(
    candidate: int,
    public_product: int,
    basis: Sequence[int],
) -> float:
    """Local completion score computed from candidate, n, and public basis only.

    For every nonzero candidate residue x modulo prime r, the complement
    n*x^{-1} exists. Consequently this score is constant on candidates that
    avoid the basis primes and cannot separate a hidden factor fibre.
    """
    compatible = 0
    for modulus in basis:
        residue = candidate % modulus
        if residue == 0:
            continue
        complement = (public_product % modulus) * pow(residue, -1, modulus)
        assert (residue * complement) % modulus == public_product % modulus
        compatible += 1
    return compatible / len(basis)


def auc(positives: Sequence[float], negatives: Sequence[float]) -> float:
    """Mann-Whitney AUC; 0.5 is chance and ties receive half credit."""
    wins = ties = total = 0
    for positive in positives:
        for negative in negatives:
            total += 1
            if positive > negative:
                wins += 1
            elif positive == negative:
                ties += 1
    return (wins + 0.5 * ties) / total if total else 0.5


def same_size_prime_nonfactors(
    factor_bits: int,
    n: int,
    p: int,
    q: int,
    rng: random.Random,
    count: int,
) -> list[int]:
    """Independent negative labels from the same prime-size distribution."""
    values: set[int] = set()
    while len(values) < count:
        candidate = random_prime(factor_bits, rng)
        if candidate in (p, q) or n % candidate == 0:
            continue
        values.add(candidate)
    return sorted(values)


@dataclass(frozen=True)
class RunRow:
    semiprime_bits: int
    trial: int
    dataset: str
    basis_name: str
    basis_hash: str
    ambiguity_log2: float
    auc_low_defect: float
    auc_structured_source: float
    auc_product_compatible: float
    positive_low_defect_mean: float
    negative_low_defect_mean: float
    positive_structured_mean: float
    negative_structured_mean: float
    positive_product_compatible_mean: float
    negative_product_compatible_mean: float
    elapsed_ms: float


def mean(values: Iterable[float]) -> float:
    return statistics.fmean(values)


def run_suite(
    bits_list: Sequence[int],
    *,
    trials: int,
    distractors: int,
    seed: int,
) -> list[RunRow]:
    rng = random.Random(seed)
    rows: list[RunRow] = []

    for bits in bits_list:
        if bits < 16 or bits > 192:
            raise ValueError("semiprime sizes must be between 16 and 192 bits")
        factor_bits = bits // 2
        for trial in range(trials):
            for dataset, structured in (
                ("unbiased", False),
                ("structured-source", True),
            ):
                n, p, q = sample_semiprime(
                    bits,
                    rng,
                    structured_source=structured,
                )
                negatives = same_size_prime_nonfactors(
                    factor_bits,
                    n,
                    p,
                    q,
                    rng,
                    distractors,
                )
                bases: dict[str, tuple[int, ...]] = {
                    "SSP15": SSP15,
                    "NON_SSP15": NON_SSP15,
                    "RANDOM15": random_control_basis(rng),
                }
                positives = (p, q)

                for basis_name, basis in bases.items():
                    started = time.perf_counter()
                    pos_low = [low_defect_score(x, basis) for x in positives]
                    neg_low = [low_defect_score(x, basis) for x in negatives]
                    pos_structured = [
                        structured_source_score(x, basis) for x in positives
                    ]
                    neg_structured = [
                        structured_source_score(x, basis) for x in negatives
                    ]
                    pos_product = [
                        product_compatible_score(x, n, basis) for x in positives
                    ]
                    neg_product = [
                        product_compatible_score(x, n, basis) for x in negatives
                    ]
                    rows.append(
                        RunRow(
                            semiprime_bits=bits,
                            trial=trial,
                            dataset=dataset,
                            basis_name=basis_name,
                            basis_hash=basis_hash(basis),
                            ambiguity_log2=product_pair_ambiguity_log2(n, basis),
                            auc_low_defect=auc(pos_low, neg_low),
                            auc_structured_source=auc(pos_structured, neg_structured),
                            auc_product_compatible=auc(pos_product, neg_product),
                            positive_low_defect_mean=mean(pos_low),
                            negative_low_defect_mean=mean(neg_low),
                            positive_structured_mean=mean(pos_structured),
                            negative_structured_mean=mean(neg_structured),
                            positive_product_compatible_mean=mean(pos_product),
                            negative_product_compatible_mean=mean(neg_product),
                            elapsed_ms=(time.perf_counter() - started) * 1000.0,
                        )
                    )
    return rows


def aggregate(
    rows: Sequence[RunRow], dataset: str, basis_name: str
) -> dict[str, float | int]:
    selected = [
        row for row in rows
        if row.dataset == dataset and row.basis_name == basis_name
    ]
    if not selected:
        raise ValueError(f"missing rows for {dataset}/{basis_name}")

    def metric(name: str) -> list[float]:
        return [float(getattr(row, name)) for row in selected]

    return {
        "auc_low_defect_mean": mean(metric("auc_low_defect")),
        "auc_low_defect_stdev": statistics.pstdev(metric("auc_low_defect")),
        "auc_structured_source_mean": mean(metric("auc_structured_source")),
        "auc_structured_source_stdev": statistics.pstdev(
            metric("auc_structured_source")
        ),
        "auc_product_compatible_mean": mean(metric("auc_product_compatible")),
        "auc_product_compatible_stdev": statistics.pstdev(
            metric("auc_product_compatible")
        ),
        "ambiguity_log2_mean": mean(metric("ambiguity_log2")),
        "positive_low_defect_mean": mean(metric("positive_low_defect_mean")),
        "negative_low_defect_mean": mean(metric("negative_low_defect_mean")),
        "positive_structured_mean": mean(metric("positive_structured_mean")),
        "negative_structured_mean": mean(metric("negative_structured_mean")),
        "row_count": len(selected),
    }


def summarize(
    rows: Sequence[RunRow],
    *,
    seed: int,
    bits_list: Sequence[int],
    trials: int,
    distractors: int,
) -> dict[str, object]:
    summary: dict[str, dict[str, dict[str, float | int]]] = {}
    for dataset in ("unbiased", "structured-source"):
        summary[dataset] = {}
        for basis_name in ("SSP15", "NON_SSP15", "RANDOM15"):
            summary[dataset][basis_name] = aggregate(rows, dataset, basis_name)

    unbiased_ssp = summary["unbiased"]["SSP15"]
    control_departure = max(
        abs(summary["unbiased"][control][metric] - 0.5)
        for control in ("NON_SSP15", "RANDOM15")
        for metric in (
            "auc_low_defect_mean",
            "auc_structured_source_mean",
            "auc_product_compatible_mean",
        )
    )
    ssp_departure = max(
        abs(unbiased_ssp[metric] - 0.5)
        for metric in (
            "auc_low_defect_mean",
            "auc_structured_source_mean",
            "auc_product_compatible_mean",
        )
    )
    product_compatibility_is_chance = math.isclose(
        unbiased_ssp["auc_product_compatible_mean"],
        0.5,
        abs_tol=1e-12,
    )
    unbiased_factor_signal = (
        ssp_departure >= 0.15
        and ssp_departure >= control_departure + 0.05
        and not product_compatibility_is_chance
    )
    structured_signal = (
        summary["structured-source"]["SSP15"][
            "auc_structured_source_mean"
        ] >= 0.80
    )

    if unbiased_factor_signal:
        verdict = "suspicious-unbiased-factor-signal-needs-independent-review"
    elif structured_signal:
        verdict = "structured-source-detector-only"
    else:
        verdict = "baseline-equivalent"

    return {
        "schema": "dashi-rsa-15ssp-fibre-admissibility-v1",
        "configuration": {
            "seed": seed,
            "semiprime_bits": list(bits_list),
            "trials_per_size": trials,
            "prime_nonfactor_distractors": distractors,
            "search_methods_used": list(SEARCH_METHODS_USED),
            "forbidden_search_methods": list(FORBIDDEN_SEARCH_METHODS),
            "factor_labels_used_only_for_evaluation": True,
        },
        "summary": summary,
        "decision": {
            "unbiased_ssp_max_auc_departure_from_chance": ssp_departure,
            "unbiased_control_max_auc_departure_from_chance": control_departure,
            "unbiased_product_compatibility_is_chance": product_compatibility_is_chance,
            "unbiased_factor_signal_observed": unbiased_factor_signal,
            "structured_source_signal_observed": structured_signal,
            "general_rsa_break_promoted": False,
            "verdict": verdict,
        },
    }


def write_csv(rows: Sequence[RunRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        raise ValueError("cannot write an empty benchmark")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(asdict(rows[0]).keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def parse_bits(value: str) -> tuple[int, ...]:
    bits = tuple(int(part.strip()) for part in value.split(",") if part.strip())
    if not bits:
        raise argparse.ArgumentTypeError("at least one bit length is required")
    return bits


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bits",
        type=parse_bits,
        default=parse_bits("32,36,40,44,48"),
    )
    parser.add_argument("--trials", type=int, default=10)
    parser.add_argument("--distractors", type=int, default=150)
    parser.add_argument("--seed", type=int, default=20260518)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path("artifacts/rsa_ssp_fibre_separation_results.csv"),
    )
    parser.add_argument(
        "--json",
        type=Path,
        default=Path("artifacts/rsa_ssp_fibre_separation_summary.json"),
    )
    args = parser.parse_args()

    if args.trials < 1 or args.distractors < 1:
        parser.error("trials and distractors must be positive")

    rows = run_suite(
        args.bits,
        trials=args.trials,
        distractors=args.distractors,
        seed=args.seed,
    )
    receipt = summarize(
        rows,
        seed=args.seed,
        bits_list=args.bits,
        trials=args.trials,
        distractors=args.distractors,
    )
    write_csv(rows, args.csv)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
