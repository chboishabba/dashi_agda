#!/usr/bin/env python3
"""Search numerical hypotheses that separate quadratic defects from near-misses.

This is a local diagnostic harness only.  It imports the candidate functionals
from ``defect_four_point_harness.py`` and tests additional candidate gates for
the unification frontier:

* parallelogram residual
* midpoint additivity of the squared defect
* second-difference bilinearity
* Clarkson-like Hilbert residuals
* polarization symmetry / PSD / Cauchy checks
* random Jensen quadraticity identities

The useful output is a fail-closed ranking of which hypotheses reject the
two-homogeneous non-Hilbert candidates while retaining seeded quadratic forms.
It does not prove ``HierarchyConsistencyGeneral`` and never promotes Clay or
terminal unification status.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Mapping, Sequence, Tuple

import defect_four_point_harness as four_point
from defect_four_point_harness import (
    Defect,
    Functional,
    add,
    dot,
    four_point_residual,
    functionals,
    l2_sq,
    random_vector,
    scale,
    sub,
)

Vector = List[float]


@dataclass
class HypothesisStats:
    name: str
    mean_abs: float
    p95_abs: float
    max_abs: float
    failures: int
    tolerance: float
    passed: bool


@dataclass
class FunctionalSearchResult:
    name: str
    expected: str
    classification: str
    hypotheses: List[HypothesisStats]
    passed_hypotheses: List[str]
    failed_hypotheses: List[str]
    rejection_power: int
    keeps_quadratic_candidate: bool
    notes: List[str]


def norm(x: Sequence[float]) -> float:
    return math.sqrt(max(l2_sq(x), 0.0))


def percentile(values: Sequence[float], pct: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    idx = min(len(ordered) - 1, max(0, round((len(ordered) - 1) * pct)))
    return ordered[idx]


def polarization(q: Defect, x: Vector, y: Vector) -> float:
    return 0.25 * (q(add(x, y)) - q(sub(x, y)))


def midpoint_additivity_residual(q: Defect, x: Vector, y: Vector) -> float:
    # For a squared norm from an inner product:
    # Q((x+y)/2) + Q((x-y)/2) = (Q(x)+Q(y))/2.
    lhs = q(scale(0.5, add(x, y))) + q(scale(0.5, sub(x, y)))
    rhs = 0.5 * (q(x) + q(y))
    return lhs - rhs


def second_difference(q: Defect, x: Vector, h: Vector) -> float:
    return q(add(x, h)) + q(sub(x, h)) - 2.0 * q(x)


def second_difference_bilinearity_residual(q: Defect, x: Vector, h: Vector, k: Vector) -> float:
    # Quadratic Q has D2_Q(x; h+k) = D2_Q(x; h) + D2_Q(x; k) + 2B(h,k),
    # where B comes from polarization and is independent of x.
    # Since D2_Q(x; h) = 2Q(h), the mixed contribution is 4B(h,k).
    return (
        second_difference(q, x, add(h, k))
        - second_difference(q, x, h)
        - second_difference(q, x, k)
        - 4.0 * polarization(q, h, k)
    )


def second_difference_translation_residual(q: Defect, x: Vector, y: Vector, h: Vector) -> float:
    # For quadratic Q, the second difference in direction h is independent of
    # the base point.
    return second_difference(q, x, h) - second_difference(q, y, h)


def clarkson_hilbert_residual(q: Defect, x: Vector, y: Vector) -> float:
    # This is the p=2 Clarkson/Hilbert parallelogram identity in midpoint form.
    return q(add(x, y)) + q(sub(x, y)) - 2.0 * q(x) - 2.0 * q(y)


def polarization_symmetry_residual(q: Defect, x: Vector, y: Vector) -> float:
    return polarization(q, x, y) - polarization(q, y, x)


def polarization_psd_residual(q: Defect, x: Vector) -> float:
    return min(0.0, polarization(q, x, x))


def polarization_diagonal_residual(q: Defect, x: Vector) -> float:
    return polarization(q, x, x) - q(x)


def polarization_cauchy_residual(q: Defect, x: Vector, y: Vector) -> float:
    # Positive means a Cauchy-Schwarz violation.
    return max(0.0, polarization(q, x, y) ** 2 - q(x) * q(y))


def polarization_additivity_residual(q: Defect, x: Vector, y: Vector, z: Vector) -> float:
    return polarization(q, add(x, y), z) - polarization(q, x, z) - polarization(q, y, z)


def jensen_quadratic_residual(q: Defect, x: Vector, y: Vector, t: float) -> float:
    # Quadratic functions satisfy this exact second-order interpolation identity.
    tx = add(scale(t, x), scale(1.0 - t, y))
    rhs = t * q(x) + (1.0 - t) * q(y) - t * (1.0 - t) * q(sub(x, y))
    return q(tx) - rhs


def normalized_abs(value: float, scale_value: float) -> float:
    return abs(value) / max(1.0, scale_value)


def sample_hypothesis_residuals(
    q: Defect,
    dim: int,
    samples: int,
    rng: random.Random,
) -> Mapping[str, List[float]]:
    residuals: Dict[str, List[float]] = {
        "parallelogram": [],
        "midpoint_additivity": [],
        "second_difference_bilinearity": [],
        "second_difference_translation": [],
        "clarkson_hilbert_residual": [],
        "polarization_symmetry": [],
        "polarization_psd": [],
        "polarization_diagonal": [],
        "polarization_cauchy": [],
        "polarization_additivity": [],
        "jensen_quadraticity": [],
    }

    for _ in range(samples):
        x = random_vector(dim, rng)
        y = random_vector(dim, rng)
        z = random_vector(dim, rng)
        h = random_vector(dim, rng)
        k = random_vector(dim, rng)
        t = rng.uniform(0.05, 0.95)

        q_scale = 1.0 + q(x) + q(y) + q(z) + q(h) + q(k)
        residuals["parallelogram"].append(
            normalized_abs(four_point_residual(q, x, y), q(x) + q(y))
        )
        residuals["midpoint_additivity"].append(
            normalized_abs(midpoint_additivity_residual(q, x, y), q(x) + q(y))
        )
        residuals["second_difference_bilinearity"].append(
            normalized_abs(second_difference_bilinearity_residual(q, x, h, k), q_scale)
        )
        residuals["second_difference_translation"].append(
            normalized_abs(second_difference_translation_residual(q, x, y, h), q_scale)
        )
        residuals["clarkson_hilbert_residual"].append(
            normalized_abs(clarkson_hilbert_residual(q, x, y), q(x) + q(y))
        )
        residuals["polarization_symmetry"].append(
            normalized_abs(polarization_symmetry_residual(q, x, y), q_scale)
        )
        residuals["polarization_psd"].append(abs(polarization_psd_residual(q, x)))
        residuals["polarization_diagonal"].append(
            normalized_abs(polarization_diagonal_residual(q, x), q(x))
        )
        residuals["polarization_cauchy"].append(
            normalized_abs(polarization_cauchy_residual(q, x, y), q(x) * q(y))
        )
        residuals["polarization_additivity"].append(
            normalized_abs(polarization_additivity_residual(q, x, y, z), q_scale)
        )
        residuals["jensen_quadraticity"].append(
            normalized_abs(jensen_quadratic_residual(q, x, y, t), q(x) + q(y) + q(sub(x, y)))
        )

    return residuals


def stats_for(name: str, values: Sequence[float], tolerance: float) -> HypothesisStats:
    failures = sum(1 for v in values if v > tolerance)
    return HypothesisStats(
        name=name,
        mean_abs=statistics.fmean(values) if values else 0.0,
        p95_abs=percentile(values, 0.95),
        max_abs=max(values) if values else 0.0,
        failures=failures,
        tolerance=tolerance,
        passed=failures == 0,
    )


def classify_result(stats: Sequence[HypothesisStats], expected: str) -> str:
    failed = {s.name for s in stats if not s.passed}
    expected_pass = expected.startswith("passes")
    if not failed and expected_pass:
        return "retained_quadratic_candidate"
    if not failed:
        return "survives_all_tested_hypotheses"
    if expected_pass:
        return "false_reject_quadratic_candidate"
    if failed == {"parallelogram", "midpoint_additivity", "clarkson_hilbert_residual"}:
        return "rejected_by_equivalent_parallelogram_family"
    if "polarization_additivity" in failed or "second_difference_bilinearity" in failed:
        return "rejected_by_bilinearity_hypothesis"
    if "jensen_quadraticity" in failed:
        return "rejected_by_jensen_quadraticity"
    return "rejected_by_tested_hypotheses"


def evaluate_functional(
    fn: Functional,
    dim: int,
    samples: int,
    seed: int,
    tolerances: Mapping[str, float],
) -> FunctionalSearchResult:
    rng = random.Random(seed)
    residuals = sample_hypothesis_residuals(fn.q, dim, samples, rng)
    stats = [stats_for(name, values, tolerances[name]) for name, values in residuals.items()]
    passed = [s.name for s in stats if s.passed]
    failed = [s.name for s in stats if not s.passed]
    classification = classify_result(stats, fn.expected)
    expected_quadratic = fn.expected.startswith("passes")
    notes: List[str] = []
    if expected_quadratic and failed:
        notes.append("warning: candidate quadratic rejected; tolerance may be too strict or hypothesis malformed")
    if (not expected_quadratic) and not failed:
        notes.append("warning: near-miss survived all sampled hypotheses")
    if (not expected_quadratic) and "parallelogram" in failed and "polarization_additivity" in failed:
        notes.append("strong signal: four-point failure appears as polarization non-additivity")
    return FunctionalSearchResult(
        name=fn.name,
        expected=fn.expected,
        classification=classification,
        hypotheses=stats,
        passed_hypotheses=passed,
        failed_hypotheses=failed,
        rejection_power=len(failed),
        keeps_quadratic_candidate=expected_quadratic and not failed,
        notes=notes,
    )


def default_tolerances(base: float) -> Dict[str, float]:
    return {
        "parallelogram": base,
        "midpoint_additivity": base,
        "second_difference_bilinearity": 2.0 * base,
        "second_difference_translation": 2.0 * base,
        "clarkson_hilbert_residual": base,
        "polarization_symmetry": base,
        "polarization_psd": base,
        "polarization_diagonal": base,
        "polarization_cauchy": 10.0 * base,
        "polarization_additivity": 2.0 * base,
        "jensen_quadraticity": 2.0 * base,
    }


def summarize(results: Sequence[FunctionalSearchResult]) -> Mapping[str, object]:
    hypothesis_rejections: Dict[str, int] = {}
    for result in results:
        is_near_miss = not result.expected.startswith("passes")
        if not is_near_miss:
            continue
        for name in result.failed_hypotheses:
            hypothesis_rejections[name] = hypothesis_rejections.get(name, 0) + 1
    ranked = sorted(hypothesis_rejections.items(), key=lambda item: (-item[1], item[0]))
    false_rejects = [r.name for r in results if r.expected.startswith("passes") and r.failed_hypotheses]
    survivors = [r.name for r in results if (not r.expected.startswith("passes")) and not r.failed_hypotheses]
    return {
        "promotion": False,
        "terminal_unification_promoted": False,
        "quadratic_false_rejects": false_rejects,
        "near_miss_survivors": survivors,
        "ranked_hypotheses_by_near_miss_rejection": [
            {"hypothesis": name, "rejected_near_miss_count": count} for name, count in ranked
        ],
        "interpretation": (
            "A useful extra hypothesis should reject non-Hilbert two-homogeneous near-misses "
            "without rejecting quadratic/SPD candidates. Numerical success is diagnostic only."
        ),
    }


def build_gluing_residual_summary(
    dim: int,
    samples: int,
    seed: int,
    hierarchy_c: float,
    search_results: Sequence[FunctionalSearchResult],
) -> Mapping[str, object]:
    """Build the deterministic frontier report for the live unification target.

    This deliberately compares two gates:

    * a coarse hierarchy-like gate: nonnegative, zero at 0, even, two-homogeneous,
      shrink-monotone, and satisfying the sampled subadditivity/coupling bound;
    * the actual four-point/parallelogram gate.

    False accepts for the coarse gate are the operational evidence that the live
    theorem cannot be ``HierarchyConsistencyGeneral`` alone.  It must be a
    gluing-residual theorem that forces four-point cancellation.
    """

    candidate_rng = random.Random(seed)
    sample_rng = random.Random(seed + 1)
    coarse_metrics = [
        four_point.sample_metrics(fn, dim, samples, sample_rng, hierarchy_c)
        for fn in four_point.functionals(dim, candidate_rng)
    ]

    coarse_gate_definition = [
        "q_nonnegative",
        "q_zero",
        "q_neg_symmetric",
        "q_nat_square_homogeneous",
        "shrink_monotonicity",
        "hierarchy_consistency",
    ]
    false_accepts = [
        m
        for m in coarse_metrics
        if m.fails_only_four_point_after_coarse_gate and not m.expected.startswith("passes")
    ]
    retained_quadratics = [
        m
        for m in coarse_metrics
        if m.expected.startswith("passes") and not m.failed_hypotheses
    ]
    coarse_rejects = [
        m
        for m in coarse_metrics
        if m.coarse_gate_failures and not m.expected.startswith("passes")
    ]
    search_by_name = {result.name: result for result in search_results}
    strengthened_rejections = [
        {
            "name": result.name,
            "classification": result.classification,
            "failed_hypotheses": result.failed_hypotheses,
            "strongest_signal": (
                "polarization_additivity"
                if "polarization_additivity" in result.failed_hypotheses
                else "jensen_quadraticity"
                if "jensen_quadraticity" in result.failed_hypotheses
                else "parallelogram"
                if "parallelogram" in result.failed_hypotheses
                else "other"
            ),
        }
        for result in search_results
        if (not result.expected.startswith("passes")) and result.failed_hypotheses
    ]

    return {
        "promotion": False,
        "terminal_unification_promoted": False,
        "diagnostic": "gluing_residual_forces_four_point_cancellation",
        "dim": dim,
        "samples": samples,
        "seed": seed,
        "hierarchy_c": hierarchy_c,
        "live_target": "GluingResidualForcesFourPointCancellation",
        "coarse_gate_definition": coarse_gate_definition,
        "coarse_gate_is_insufficient": bool(false_accepts),
        "coarse_gate_false_accept_count": len(false_accepts),
        "coarse_gate_false_accepts": [
            {
                "name": m.name,
                "classification": m.classification,
                "max_abs_four_point": m.max_abs_four_point,
                "p95_abs_four_point": m.p95_abs_four_point,
                "hierarchy_c_needed_999": m.hierarchy_c_needed_max,
                "failed_hypotheses": list(m.failed_hypotheses),
                "expected": m.expected,
                "strengthened_search_failed_hypotheses": (
                    search_by_name[m.name].failed_hypotheses if m.name in search_by_name else []
                ),
            }
            for m in false_accepts
        ],
        "quadratic_controls_retained": [
            {
                "name": m.name,
                "max_abs_four_point": m.max_abs_four_point,
                "hierarchy_c_needed_999": m.hierarchy_c_needed_max,
            }
            for m in retained_quadratics
        ],
        "coarse_gate_rejects_before_four_point": [
            {
                "name": m.name,
                "coarse_gate_failures": list(m.coarse_gate_failures),
                "failed_hypotheses": list(m.failed_hypotheses),
                "expected": m.expected,
            }
            for m in coarse_rejects
        ],
        "strengthened_hypothesis_rejections": strengthened_rejections,
        "conclusion": (
            "Sampled homogeneity/monotonicity/subadditivity-like checks false-accept "
            "non-Hilbert two-homogeneous candidates. The live proof obligation is a "
            "gluing-residual statement strong enough to force the four-point/"
            "parallelogram cancellation, not another coarse hierarchy bound."
        ),
        "residual_risk": (
            "Numerical harness only. It supplies deterministic counterexample "
            "diagnostics for candidate hypotheses and does not prove the Agda boundary."
        ),
    }


def print_report(results: Sequence[FunctionalSearchResult], summary: Mapping[str, object]) -> None:
    print("defect hierarchy hypothesis search")
    print("diagnostic only: promotion=false terminal_unification_promoted=false")
    print()
    print("{:<34} {:<42} {:>8}  {}".format("functional", "classification", "rejects", "failed hypotheses"))
    for result in results:
        failed = ",".join(result.failed_hypotheses) if result.failed_hypotheses else "none"
        print(
            "{:<34} {:<42} {:>8}  {}".format(
                result.name,
                result.classification,
                result.rejection_power,
                failed,
            )
        )
    print()
    print("ranked hypotheses")
    for item in summary["ranked_hypotheses_by_near_miss_rejection"]:
        print(f"- {item['hypothesis']}: rejected {item['rejected_near_miss_count']} near-miss candidates")
    if summary["quadratic_false_rejects"]:
        print()
        print("quadratic false rejects:", ", ".join(summary["quadratic_false_rejects"]))
    if summary["near_miss_survivors"]:
        print()
        print("near-miss survivors:", ", ".join(summary["near_miss_survivors"]))


def write_json(path: Path, payload: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dim", type=int, default=5)
    parser.add_argument("--samples", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--tolerance", type=float, default=1.0e-8)
    parser.add_argument(
        "--hierarchy-c",
        type=float,
        default=2.0,
        help="coarse hierarchy inequality constant used in the gluing residual summary",
    )
    parser.add_argument("--json", dest="json_path", help="write JSON report to this path")
    parser.add_argument(
        "--gluing-summary-json",
        default="outputs/gluing_residual_forces_four_point_cancellation_summary.json",
        help=(
            "write deterministic coarse-gate insufficiency report for "
            "GluingResidualForcesFourPointCancellation; use empty string to disable"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.dim <= 0:
        raise SystemExit("--dim must be positive")
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.tolerance <= 0.0:
        raise SystemExit("--tolerance must be positive")
    if args.hierarchy_c < 0.0:
        raise SystemExit("--hierarchy-c must be nonnegative")

    candidate_rng = random.Random(args.seed)
    candidates = functionals(args.dim, candidate_rng)
    tolerances = default_tolerances(args.tolerance)
    results = [
        evaluate_functional(fn, args.dim, args.samples, args.seed + 1009 * (idx + 1), tolerances)
        for idx, fn in enumerate(candidates)
    ]
    summary = summarize(results)
    payload = {
        "promotion": False,
        "terminal_unification_promoted": False,
        "diagnostic": "defect_hierarchy_hypothesis_search",
        "dim": args.dim,
        "samples": args.samples,
        "seed": args.seed,
        "tolerances": tolerances,
        "summary": summary,
        "results": [asdict(result) for result in results],
    }
    print_report(results, summary)
    if args.json_path:
        write_json(Path(args.json_path), payload)
        print()
        print(f"wrote json: {args.json_path}")
    if args.gluing_summary_json:
        gluing_summary = build_gluing_residual_summary(
            args.dim,
            args.samples,
            args.seed,
            args.hierarchy_c,
            results,
        )
        write_json(Path(args.gluing_summary_json), gluing_summary)
        print(f"wrote gluing summary: {args.gluing_summary_json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
