#!/usr/bin/env python3
"""YM weak-coupling polymer ratio and sum diagnostic.

This pure-stdlib harness encodes the finite arithmetic surface used by the
weak-coupling polymer sum argument.  It is deliberately diagnostic only: it
computes a tuned activity parameter ``a``, the polymer ratio, the weak-coupling
threshold, the geometric sum/tail bounds, and sample pass/fail cases.

The constants are kept explicit in the payload:

* ``8e`` is the convergence-scale majorant.
* ``16e`` is the strict weak-coupling majorant.

Nothing emitted here is a theorem certificate or a promotion signal.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


EIGHT_E = 8.0 * math.e
SIXTEEN_E = 16.0 * math.e
EPS = 1.0e-15


@dataclass(frozen=True)
class PolymerCase:
    name: str
    classification: str
    beta: float
    c_min: float
    tuned_a: float
    convergence_scale: float
    strict_scale: float
    ratio_8e: float
    strict_ratio_16e: float
    geometric_sum_bound: float
    geometric_tail_bound: float
    tail_prefix: int
    convergence_threshold_beta: float
    strict_threshold_beta: float
    beta_margin_to_convergence_threshold: float
    beta_margin_to_strict_threshold: float
    observed_pass: bool
    expected_pass: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--beta-reference",
        type=float,
        default=6.0,
        help="Reference beta used to tune the activity offset a.",
    )
    parser.add_argument(
        "--c-min",
        type=float,
        default=1.0,
        help="Minimum contour/action coefficient in the exponent.",
    )
    parser.add_argument(
        "--strict-margin",
        type=float,
        default=0.25,
        help="How far above the strict 16e threshold the reference case is tuned.",
    )
    parser.add_argument(
        "--convergence-scale",
        type=float,
        default=EIGHT_E,
        help="Convergence majorant scale; defaults to 8e.",
    )
    parser.add_argument(
        "--strict-scale",
        type=float,
        default=SIXTEEN_E,
        help="Strict weak-coupling majorant scale; defaults to 16e.",
    )
    parser.add_argument(
        "--tail-prefix",
        type=int,
        default=4,
        help="Number of prefix terms absorbed before the geometric tail.",
    )
    parser.add_argument(
        "--sample-fraction",
        type=float,
        default=0.05,
        help="Relative offset used to generate below/at/above threshold samples.",
    )
    parser.add_argument(
        "--json-output",
        type=Path,
        default=None,
        help="Optional path for a copy of the JSON payload.",
    )
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.beta_reference <= 0.0:
        raise ValueError("--beta-reference must be positive")
    if args.c_min <= 0.0:
        raise ValueError("--c-min must be positive")
    if args.strict_margin < 0.0:
        raise ValueError("--strict-margin must be non-negative")
    if args.convergence_scale <= 0.0:
        raise ValueError("--convergence-scale must be positive")
    if args.strict_scale <= args.convergence_scale:
        raise ValueError("--strict-scale must exceed --convergence-scale")
    if args.tail_prefix < 0:
        raise ValueError("--tail-prefix must be non-negative")
    if not (0.0 < args.sample_fraction < 0.5):
        raise ValueError("--sample-fraction must satisfy 0 < fraction < 0.5")


def safe_exp(value: float) -> float:
    try:
        return math.exp(value)
    except OverflowError:
        return math.inf


def tuned_a(
    beta_reference: float,
    c_min: float,
    strict_scale: float,
    strict_margin: float,
) -> float:
    return beta_reference * c_min - math.log(strict_scale) - strict_margin


def ratio(beta: float, a: float, c_min: float, scale: float) -> float:
    return scale * safe_exp(a - beta * c_min)


def geometric_sum_bound(r: float) -> float:
    if not math.isfinite(r) or r < 0.0:
        return math.nan
    if r >= 1.0:
        return math.inf
    return r / (1.0 - r)


def geometric_tail_bound(r: float, prefix_terms: int) -> float:
    if not math.isfinite(r) or r < 0.0:
        return math.nan
    if r >= 1.0:
        return math.inf
    return r ** (prefix_terms + 1) / (1.0 - r)


def threshold_beta(a: float, c_min: float, scale: float) -> float:
    return (a + math.log(scale)) / c_min


def make_case(
    *,
    name: str,
    classification: str,
    beta: float,
    tuned_a_value: float,
    c_min: float,
    convergence_scale: float,
    strict_scale: float,
    tail_prefix: int,
    strict_threshold: float,
    convergence_threshold: float,
) -> PolymerCase:
    ratio_8e = ratio(beta, tuned_a_value, c_min, convergence_scale)
    strict_ratio_16e = ratio(beta, tuned_a_value, c_min, strict_scale)
    sum_bound = geometric_sum_bound(ratio_8e)
    tail_bound = geometric_tail_bound(ratio_8e, tail_prefix)
    observed_pass = strict_ratio_16e <= 1.0 and math.isfinite(sum_bound)
    expected_pass = beta >= strict_threshold
    return PolymerCase(
        name=name,
        classification=classification,
        beta=beta,
        c_min=c_min,
        tuned_a=tuned_a_value,
        convergence_scale=convergence_scale,
        strict_scale=strict_scale,
        ratio_8e=ratio_8e,
        strict_ratio_16e=strict_ratio_16e,
        geometric_sum_bound=sum_bound,
        geometric_tail_bound=tail_bound,
        tail_prefix=tail_prefix,
        convergence_threshold_beta=convergence_threshold,
        strict_threshold_beta=strict_threshold,
        beta_margin_to_convergence_threshold=beta - convergence_threshold,
        beta_margin_to_strict_threshold=beta - strict_threshold,
        observed_pass=observed_pass,
        expected_pass=expected_pass,
        checks={
            "finite_ratio": math.isfinite(ratio_8e),
            "finite_tail": math.isfinite(tail_bound),
            "ratio_below_one": ratio_8e < 1.0,
            "strict_ratio_below_one": strict_ratio_16e < 1.0,
            "weak_coupling_passes": observed_pass,
            "expected_outcome_observed": observed_pass == expected_pass,
        },
    )


def build_cases(args: argparse.Namespace) -> tuple[float, float, float, list[PolymerCase]]:
    a_value = tuned_a(
        beta_reference=args.beta_reference,
        c_min=args.c_min,
        strict_scale=args.strict_scale,
        strict_margin=args.strict_margin,
    )
    convergence_threshold = threshold_beta(a_value, args.c_min, args.convergence_scale)
    strict_threshold = threshold_beta(a_value, args.c_min, args.strict_scale)

    below_beta = strict_threshold * (1.0 - args.sample_fraction)
    at_beta = strict_threshold
    above_beta = strict_threshold * (1.0 + args.sample_fraction)

    reference_case = make_case(
        name="reference_tune",
        classification="reference_tuned_safe",
        beta=args.beta_reference,
        tuned_a_value=a_value,
        c_min=args.c_min,
        convergence_scale=args.convergence_scale,
        strict_scale=args.strict_scale,
        tail_prefix=args.tail_prefix,
        strict_threshold=strict_threshold,
        convergence_threshold=convergence_threshold,
    )
    sample_cases = [
        make_case(
            name="below_threshold",
            classification="sample_fail",
            beta=below_beta,
            tuned_a_value=a_value,
            c_min=args.c_min,
            convergence_scale=args.convergence_scale,
            strict_scale=args.strict_scale,
            tail_prefix=args.tail_prefix,
            strict_threshold=strict_threshold,
            convergence_threshold=convergence_threshold,
        ),
        make_case(
            name="at_threshold",
            classification="sample_boundary_pass",
            beta=at_beta,
            tuned_a_value=a_value,
            c_min=args.c_min,
            convergence_scale=args.convergence_scale,
            strict_scale=args.strict_scale,
            tail_prefix=args.tail_prefix,
            strict_threshold=strict_threshold,
            convergence_threshold=convergence_threshold,
        ),
        make_case(
            name="above_threshold",
            classification="sample_pass",
            beta=above_beta,
            tuned_a_value=a_value,
            c_min=args.c_min,
            convergence_scale=args.convergence_scale,
            strict_scale=args.strict_scale,
            tail_prefix=args.tail_prefix,
            strict_threshold=strict_threshold,
            convergence_threshold=convergence_threshold,
        ),
    ]
    return a_value, convergence_threshold, strict_threshold, [reference_case, *sample_cases]


def summary_payload(
    args: argparse.Namespace,
    tuned_a_value: float,
    convergence_threshold: float,
    strict_threshold: float,
    cases: list[PolymerCase],
) -> dict[str, object]:
    reference_case = cases[0]
    sample_cases = cases[1:]
    return {
        "contract": "ym_weak_coupling_polymer_sum_bound",
        "diagnostic_only": True,
        "promotion": {
            "ym_clay_promoted": False,
            "continuum_yang_mills_promoted": False,
            "polymer_sum_theorem_promoted": False,
        },
        "proof_constants": {
            "convergence_scale_8e": args.convergence_scale,
            "strict_scale_16e": args.strict_scale,
            "convergence_scale_formula": "8e",
            "strict_scale_formula": "16e",
        },
        "tuning": {
            "beta_reference": args.beta_reference,
            "c_min": args.c_min,
            "strict_margin": args.strict_margin,
            "tuned_a": tuned_a_value,
            "tuned_a_formula": "beta_reference*c_min - log(strict_scale) - strict_margin",
        },
        "thresholds": {
            "convergence_beta": convergence_threshold,
            "strict_weak_coupling_beta": strict_threshold,
            "convergence_beta_formula": "(a + log(convergence_scale))/c_min",
            "strict_beta_formula": "(a + log(strict_scale))/c_min",
        },
        "reference_case": asdict(reference_case),
        "sample_cases": [asdict(case) for case in sample_cases],
        "summary": {
            "all_cases_finite": all(
                math.isfinite(case.ratio_8e)
                and math.isfinite(case.strict_ratio_16e)
                and math.isfinite(case.geometric_tail_bound)
                for case in cases
            ),
            "all_sample_outcomes_match_expected": all(
                case.observed_pass == case.expected_pass for case in sample_cases
            ),
            "sample_pass_count": sum(1 for case in sample_cases if case.observed_pass),
            "sample_fail_count": sum(1 for case in sample_cases if not case.observed_pass),
            "any_sample_pass": any(case.observed_pass for case in sample_cases),
            "any_sample_fail": any(not case.observed_pass for case in sample_cases),
            "reference_passes": reference_case.observed_pass,
            "reference_margin_to_strict_threshold": reference_case.beta_margin_to_strict_threshold,
            "reference_ratio_8e": reference_case.ratio_8e,
            "reference_tail_bound": reference_case.geometric_tail_bound,
            "threshold_gap_strict_minus_convergence": strict_threshold - convergence_threshold,
            "threshold_ordering_ok": strict_threshold > convergence_threshold,
            "tail_prefix": args.tail_prefix,
        },
    }


def write_output(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    tuned_a_value, convergence_threshold, strict_threshold, cases = build_cases(args)
    payload = summary_payload(args, tuned_a_value, convergence_threshold, strict_threshold, cases)
    if args.json_output is not None:
        write_output(args.json_output, payload)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
