#!/usr/bin/env python3
"""Deterministic counterexample search over the repo-native prime-profile carrier.

The search is intentionally bounded and diagnostic:
- it adapts the existing prototype examples into MoonshinePrimeState payloads,
- parses the repo-native 15-prime carrier,
- reports finite profile diagnostics, and
- checks any arithmetic candidate inequalities only when the relevant numeric
  fields are present in the input payload.

This script does not prove any inequality; it only reports whether a finite
sample violates the checked candidate bounds.
"""

from __future__ import annotations

import argparse
import collections
import itertools
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable

from moonshine_prime_from_prototype import adapt
from moonshine_prime_object import SSP_PRIMES, observe, parse_state

DEFAULT_INPUTS = (
    Path("scripts/examples/near_miss_state.json"),
    Path("scripts/examples/head_on_state.json"),
)

CANDIDATE_PAIRS = (
    ("weightedPressure", "weightedSupport"),
    ("totalPressure", "trackedSupport"),
    ("totalPressure", "radicalSupportOfPair"),
)
TOP_CASE_LIMIT = 3
LARGE_DELTA_THRESHOLD = 2
THRESHOLDS = (2, 3, 4)


@dataclass(frozen=True)
class CandidateCheck:
    left: str
    right: str
    left_value: float | int | None
    right_value: float | int | None
    present: bool
    violated: bool | None


@dataclass(frozen=True)
class CooccurrenceSummary:
    threshold: int
    support: list[int]
    support_count: int
    pair_count: int
    triple_count: int
    pairs: list[str]
    triples: list[str]


def summarize_threshold_signature(delta_values: list[int], thresholds: Iterable[int] = THRESHOLDS) -> str:
    counts = summarize_threshold_counts(delta_values, thresholds)
    ordered_thresholds = sorted(counts, key=int)
    return "|".join(f"{threshold}:{counts[threshold]}" for threshold in ordered_thresholds)


def build_threshold_diagnostics(
    delta_values: list[int],
    thresholds: Iterable[int] = THRESHOLDS,
) -> dict[str, Any]:
    threshold_counts = summarize_threshold_counts(delta_values, thresholds)
    pair_thresholds = summarize_pair_thresholds(delta_values, thresholds)
    shared_budget = summarize_shared_budget(delta_values, thresholds)
    return {
        "threshold_counts": threshold_counts,
        "pair_thresholds": pair_thresholds,
        "shared_budget": shared_budget,
        "threshold_signature": summarize_threshold_signature(delta_values, thresholds),
        "shared_budget_trend": summarize_budget_trend(shared_budget),
        "shared_budget_decay": summarize_shared_budget_decay(shared_budget),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "inputs",
        nargs="*",
        help="Prototype or MoonshinePrimeState JSON files to inspect",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print the JSON report",
    )
    return parser.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must decode to a JSON object")
    return payload


def normalize_payload(payload: dict[str, Any]) -> dict[str, Any]:
    required = {"carrier", "signature", "eigenProfile", "basinLabel", "factorVector", "mdlLevel"}
    if required.issubset(payload):
        return payload
    if "delta" in payload:
        return adapt(payload)
    raise ValueError(
        "payload is neither a MoonshinePrimeState nor a prototype state with a delta vector"
    )


def candidate_check(payload: dict[str, Any], left: str, right: str) -> CandidateCheck:
    left_value = payload.get(left)
    right_value = payload.get(right)
    if left_value is None or right_value is None:
        return CandidateCheck(left, right, left_value, right_value, False, None)
    if not isinstance(left_value, (int, float)) or not isinstance(right_value, (int, float)):
        return CandidateCheck(left, right, left_value, right_value, False, None)
    return CandidateCheck(left, right, left_value, right_value, True, float(left_value) > float(right_value))


def summarize_cooccurrence(delta_values: list[int], threshold: int) -> CooccurrenceSummary:
    support = [int(p) for p, value in zip(SSP_PRIMES, delta_values) if value >= threshold]
    pair_count = len(support) * (len(support) - 1) // 2
    triple_count = len(support) * (len(support) - 1) * (len(support) - 2) // 6
    pairs = [f"{a}-{b}" for a, b in itertools.combinations(support, 2)]
    triples = [f"{a}-{b}-{c}" for a, b, c in itertools.combinations(support, 3)]
    return CooccurrenceSummary(
        threshold=threshold,
        support=support,
        support_count=len(support),
        pair_count=pair_count,
        triple_count=triple_count,
        pairs=pairs,
        triples=triples,
    )


def summarize_threshold_counts(delta_values: list[int], thresholds: Iterable[int] = THRESHOLDS) -> dict[str, int]:
    return {
        str(threshold): sum(1 for value in delta_values if value >= threshold)
        for threshold in thresholds
    }


def summarize_pair_thresholds(delta_values: list[int], thresholds: Iterable[int] = THRESHOLDS) -> dict[str, dict[str, int]]:
    summaries: dict[str, dict[str, int]] = {}
    for threshold in thresholds:
        support_count = sum(1 for value in delta_values if value >= threshold)
        summaries[str(threshold)] = {
            "support_count": support_count,
            "pair_count": support_count * (support_count - 1) // 2,
            "triple_count": support_count * (support_count - 1) * (support_count - 2) // 6,
        }
    return summaries


def summarize_shared_budget(delta_values: list[int], thresholds: Iterable[int] = THRESHOLDS) -> dict[str, dict[str, int]]:
    budget: dict[str, dict[str, int]] = {}
    for threshold in thresholds:
        support_count = sum(1 for value in delta_values if value >= threshold)
        pair_count = support_count * (support_count - 1) // 2
        triple_count = support_count * (support_count - 1) * (support_count - 2) // 6
        budget[str(threshold)] = {
            "support_count": support_count,
            "pair_count": pair_count,
            "triple_count": triple_count,
            "budget_mass": threshold * support_count,
        }
    return budget


def summarize_budget_trend(shared_budget: dict[str, dict[str, int]]) -> dict[str, bool]:
    ordered_thresholds = sorted(shared_budget, key=int)
    support_counts = [shared_budget[str(threshold)]["support_count"] for threshold in ordered_thresholds]
    pair_counts = [shared_budget[str(threshold)]["pair_count"] for threshold in ordered_thresholds]
    triple_counts = [shared_budget[str(threshold)]["triple_count"] for threshold in ordered_thresholds]

    def nonincreasing(values: list[int]) -> bool:
        return all(left >= right for left, right in zip(values, values[1:]))

    return {
        "support_count_nonincreasing": nonincreasing(support_counts),
        "pair_count_nonincreasing": nonincreasing(pair_counts),
        "triple_count_nonincreasing": nonincreasing(triple_counts),
    }


def summarize_shared_budget_decay(shared_budget: dict[str, dict[str, int]]) -> dict[str, dict[str, float | int]]:
    ordered_thresholds = sorted(shared_budget, key=int)
    decay: dict[str, dict[str, float | int]] = {}
    previous_threshold: str | None = None
    for threshold in ordered_thresholds:
        current = shared_budget[threshold]
        if previous_threshold is None:
            decay[threshold] = {
                "support_count": current["support_count"],
                "pair_count": current["pair_count"],
                "triple_count": current["triple_count"],
                "support_drop": 0,
                "pair_drop": 0,
                "triple_drop": 0,
                "support_retention": 1.0,
                "pair_retention": 1.0,
                "triple_retention": 1.0,
            }
        else:
            previous = shared_budget[previous_threshold]
            support_count = current["support_count"]
            pair_count = current["pair_count"]
            triple_count = current["triple_count"]
            prev_support = previous["support_count"]
            prev_pair = previous["pair_count"]
            prev_triple = previous["triple_count"]
            decay[threshold] = {
                "support_count": support_count,
                "pair_count": pair_count,
                "triple_count": triple_count,
                "support_drop": prev_support - support_count,
                "pair_drop": prev_pair - pair_count,
                "triple_drop": prev_triple - triple_count,
                "support_retention": support_count / prev_support if prev_support else 0.0,
                "pair_retention": pair_count / prev_pair if prev_pair else 0.0,
                "triple_retention": triple_count / prev_triple if prev_triple else 0.0,
            }
        previous_threshold = threshold
    return decay


def summarize_top_cases(reports: list[dict[str, Any]], limit: int = TOP_CASE_LIMIT) -> list[dict[str, Any]]:
    top_reports = sorted(
        reports,
        key=lambda report: (
            -report["weighted_max_pressure"],
            -report["interaction_mass"],
            -report["active_wall_count"],
            report["input"],
        ),
    )[:limit]
    return [
        {
            "input": report["input"],
            "weighted_max_pressure": report["weighted_max_pressure"],
            "interaction_mass": report["interaction_mass"],
            "active_wall_count": report["active_wall_count"],
            "max_delta": report["max_delta"],
            "max_delta_prime": report["max_delta_prime"],
            "large_delta_count": report["large_delta_count"],
            "mass_above_1": report["mass_above_1"],
            "mass_above_2": report["mass_above_2"],
            "dominance_ratio": report["dominance_ratio"],
            "large_delta_ge2": report["large_delta_ge2"],
            "large_delta_pairs_ge2": report["large_delta_pairs_ge2"],
            "large_delta_triples_ge2": report["large_delta_triples_ge2"],
            "pair_thresholds": report["pair_thresholds"],
            "shared_budget": report["shared_budget"],
            "threshold_signature": report["threshold_signature"],
            "threshold_diagnostics": report["threshold_diagnostics"],
        }
        for report in top_reports
    ]


def group_reports_by_threshold_signature(reports: list[dict[str, Any]], limit: int = TOP_CASE_LIMIT) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    for report in reports:
        grouped[report["threshold_signature"]].append(report)

    output: list[dict[str, Any]] = []
    for signature, group in sorted(
        grouped.items(),
        key=lambda item: (
            -len(item[1]),
            -max(report["weighted_max_pressure"] for report in item[1]),
            item[0],
        ),
    ):
        ordered_group = sorted(
            group,
            key=lambda report: (
                -report["weighted_max_pressure"],
                -report["interaction_mass"],
                report["input"],
            ),
        )[:limit]
        output.append(
            {
                "threshold_signature": signature,
                "count": len(group),
                "max_weighted_max_pressure": max(report["weighted_max_pressure"] for report in group),
                "max_interaction_mass": max(report["interaction_mass"] for report in group),
                "top_cases": [
                    {
                        "input": report["input"],
                        "weighted_max_pressure": report["weighted_max_pressure"],
                        "interaction_mass": report["interaction_mass"],
                        "active_wall_count": report["active_wall_count"],
                        "large_delta_count": report["large_delta_count"],
                        "threshold_counts": report["threshold_counts"],
                        "pair_thresholds": report["pair_thresholds"],
                        "shared_budget": report["shared_budget"],
                        "threshold_diagnostics": report["threshold_diagnostics"],
                    }
                    for report in ordered_group
                ],
            }
        )
    return output


def summarize_run(reports: list[dict[str, Any]]) -> dict[str, Any]:
    if not reports:
        return {
            "max_weighted_max_pressure": 0,
            "max_interaction_mass": 0,
            "mean_interaction_mass": 0.0,
            "reports_with_large_delta_pair": 0,
            "reports_with_large_delta_triple": 0,
            "threshold_counts": {},
            "pair_thresholds": {},
            "shared_budget": {},
            "shared_budget_trend": {},
            "shared_budget_decay": {},
            "threshold_diagnostics": {},
        }
    interaction_masses = [report["interaction_mass"] for report in reports]
    large_pair_reports = sum(1 for report in reports if report["large_delta_ge2"]["pair_count"] > 0)
    large_triple_reports = sum(1 for report in reports if report["large_delta_ge2"]["triple_count"] > 0)
    threshold_counts: dict[str, int] = {}
    pair_thresholds: dict[str, dict[str, int]] = {}
    for threshold in THRESHOLDS:
        threshold_counts[str(threshold)] = sum(report["threshold_counts"][str(threshold)] for report in reports)
        pair_thresholds[str(threshold)] = {
            "support_count": sum(report["pair_thresholds"][str(threshold)]["support_count"] for report in reports),
            "pair_count": sum(report["pair_thresholds"][str(threshold)]["pair_count"] for report in reports),
            "triple_count": sum(report["pair_thresholds"][str(threshold)]["triple_count"] for report in reports),
        }
    shared_budget = {
        str(threshold): {
            "support_count": sum(report["shared_budget"][str(threshold)]["support_count"] for report in reports),
            "pair_count": sum(report["shared_budget"][str(threshold)]["pair_count"] for report in reports),
            "triple_count": sum(report["shared_budget"][str(threshold)]["triple_count"] for report in reports),
            "budget_mass": sum(report["shared_budget"][str(threshold)]["budget_mass"] for report in reports),
        }
        for threshold in THRESHOLDS
    }
    return {
        "max_weighted_max_pressure": max(report["weighted_max_pressure"] for report in reports),
        "max_interaction_mass": max(interaction_masses),
        "mean_interaction_mass": sum(interaction_masses) / len(interaction_masses),
        "reports_with_large_delta_pair": large_pair_reports,
        "reports_with_large_delta_triple": large_triple_reports,
        "threshold_counts": threshold_counts,
        "pair_thresholds": pair_thresholds,
        "shared_budget": shared_budget,
        "shared_budget_trend": summarize_budget_trend(shared_budget),
        "shared_budget_decay": summarize_shared_budget_decay(shared_budget),
        "threshold_diagnostics": {
            "threshold_counts": threshold_counts,
            "pair_thresholds": pair_thresholds,
            "shared_budget": shared_budget,
            "shared_budget_trend": summarize_budget_trend(shared_budget),
            "shared_budget_decay": summarize_shared_budget_decay(shared_budget),
        },
    }


def group_top_cases_by_max_delta(reports: list[dict[str, Any]], limit: int = TOP_CASE_LIMIT) -> list[dict[str, Any]]:
    grouped: dict[int, list[dict[str, Any]]] = collections.defaultdict(list)
    for report in reports:
        grouped[int(report["max_delta"])].append(report)

    output: list[dict[str, Any]] = []
    for max_delta in sorted(grouped, reverse=True):
        group = sorted(
            grouped[max_delta],
            key=lambda report: (
                -report["weighted_max_pressure"],
                -report["interaction_mass"],
                report["input"],
            ),
        )[:limit]
        output.append(
            {
                "max_delta": max_delta,
                "count": len(grouped[max_delta]),
                "top_cases": [
                    {
                        "input": report["input"],
                        "weighted_max_pressure": report["weighted_max_pressure"],
                        "interaction_mass": report["interaction_mass"],
                        "active_wall_count": report["active_wall_count"],
                        "large_delta_count": report["large_delta_count"],
                        "threshold_counts": report["threshold_counts"],
                        "pair_thresholds": report["pair_thresholds"],
                        "shared_budget": report["shared_budget"],
                        "threshold_diagnostics": report["threshold_diagnostics"],
                    }
                    for report in group
                ],
            }
        )
    return output


def build_search_report(path: Path) -> dict[str, Any]:
    raw = load_json(path)
    normalized = normalize_payload(raw)
    state = parse_state(normalized)
    observed = observe(state)

    profile_checks = [
        {
            "name": "support_weight_nonnegative",
            "value": int(observed.factor_support_weight),
            "passed": int(observed.factor_support_weight) >= 0,
        },
        {
            "name": "support_subset_canonical",
            "value": list(observed.factor_support),
            "passed": all(p in SSP_PRIMES for p in observed.factor_support),
        },
        {
            "name": "signature_subset_canonical",
            "value": [p for p in SSP_PRIMES if observed.signature[p]],
            "passed": True,
        },
    ]

    arithmetic_checks = [candidate_check(normalized, left, right) for left, right in CANDIDATE_PAIRS]
    checked = [check for check in arithmetic_checks if check.present]
    violations = [
        {
            "left": check.left,
            "right": check.right,
            "left_value": check.left_value,
            "right_value": check.right_value,
        }
        for check in checked
        if check.violated
    ]

    factor_vector = observed.factor_vector
    delta_values = [int(factor_vector[p]) for p in SSP_PRIMES]
    active_wall_count = sum(1 for p in SSP_PRIMES if int(factor_vector[p]) > 0)
    max_delta = max(delta_values, default=0)
    max_delta_prime = (
        next((int(p) for p in SSP_PRIMES if int(factor_vector[p]) == max_delta), None)
        if max_delta > 0
        else None
    )
    large_delta_count = sum(1 for value in delta_values if value >= LARGE_DELTA_THRESHOLD)
    mass_above_1 = large_delta_count
    mass_above_2 = sum(1 for value in delta_values if value >= 3)
    dominance_ratio = max_delta / max(1, active_wall_count)
    weighted_max_pressure = max((int(p) * int(factor_vector[p]) for p in SSP_PRIMES), default=0)
    weighted_pressure_sum = sum(int(p) * int(factor_vector[p]) for p in SSP_PRIMES)
    interaction_mass = sum(value * value for value in delta_values)
    large_delta_ge2 = summarize_cooccurrence(delta_values, LARGE_DELTA_THRESHOLD)
    threshold_counts = summarize_threshold_counts(delta_values)
    pair_thresholds = summarize_pair_thresholds(delta_values)
    shared_budget = summarize_shared_budget(delta_values)
    threshold_signature = summarize_threshold_signature(delta_values)
    threshold_diagnostics = build_threshold_diagnostics(delta_values)
    delta_histogram = {
        str(delta): count
        for delta, count in sorted(collections.Counter(delta_values).items())
    }

    return {
        "input": str(path),
        "normalized_kind": "moonshine_prime_state" if raw is normalized else "prototype_state_adapted",
        "basin_label": observed.basin_label,
        "factor_support": list(observed.factor_support),
        "factor_support_weight": int(observed.factor_support_weight),
        "active_wall_count": active_wall_count,
        "max_delta": max_delta,
        "large_delta_count": large_delta_count,
        "mass_above_1": mass_above_1,
        "mass_above_2": mass_above_2,
        "dominance_ratio": dominance_ratio,
        "interaction_mass": interaction_mass,
        "threshold_counts": threshold_counts,
        "pair_thresholds": pair_thresholds,
        "shared_budget": shared_budget,
        "shared_budget_trend": summarize_budget_trend(shared_budget),
        "shared_budget_decay": summarize_shared_budget_decay(shared_budget),
        "threshold_signature": threshold_signature,
        "threshold_diagnostics": threshold_diagnostics,
        "delta_histogram": delta_histogram,
        "weighted_max_pressure": weighted_max_pressure,
        "weighted_pressure_sum": weighted_pressure_sum,
        "max_delta_prime": max_delta_prime,
        "large_delta_ge2": asdict(large_delta_ge2),
        "large_delta_pairs_ge2": large_delta_ge2.pairs,
        "large_delta_triples_ge2": large_delta_ge2.triples,
        "profile_checks": profile_checks,
        "arithmetic_checks": [asdict(check) for check in arithmetic_checks],
        "violations": violations,
        "passes": not violations,
    }


def default_inputs() -> list[Path]:
    candidates = [path for path in DEFAULT_INPUTS if path.exists()]
    return candidates


def main() -> int:
    args = parse_args()
    inputs = [Path(value) for value in args.inputs] if args.inputs else default_inputs()
    if not inputs:
        raise SystemExit("no input files found; pass one or more JSON files explicitly")

    reports = [build_search_report(path) for path in inputs]
    output = {
        "checked_inputs": [str(path) for path in inputs],
        "search_space_size": len(reports),
        "checked_pairs": [f"{left}<={right}" for left, right in CANDIDATE_PAIRS],
        "reports": reports,
        "top_cases": summarize_top_cases(reports),
        "top_cases_by_max_delta": group_top_cases_by_max_delta(reports),
        "cases_by_threshold_signature": group_reports_by_threshold_signature(reports),
        "run_summary": summarize_run(reports),
        "counterexample_found": any(report["violations"] for report in reports),
    }

    text = json.dumps(output, indent=2 if args.pretty else None, sort_keys=True)
    print(text)
    return 1 if output["counterexample_found"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
