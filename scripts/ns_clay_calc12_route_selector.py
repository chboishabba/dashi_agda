#!/usr/bin/env python3
"""Deterministic Calc 12 route selector for power-law fitting.

This CLI reads precomputed pair data, filters to finite positive pairs, fits

    log(omega_e2_sq) = log_C + beta * log(g12)

with ordinary least squares, and emits a conservative JSON decision packet.
It is a diagnostic selector only: proof blocking remains false, theorem
authority remains false, and Clay promotion remains false.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


CALC = "Calc12"
DEFAULT_OUTPUT = Path("outputs") / "ns_clay_calc12_route_selector.json"
CI_Z_95 = 1.96


class InputError(ValueError):
    """Raised when the input JSON does not match the selector contract."""


@dataclass(frozen=True)
class PairFit:
    datum_id: Any
    n_pairs_raw: int
    n_pairs_used: int
    min_g12_observed: float
    log_C: float
    fitted_C: float
    beta: float
    r_squared: float
    standard_error_beta: float
    beta_ci_95: tuple[float, float]
    decision: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "datum_id": self.datum_id,
            "n_pairs_raw": self.n_pairs_raw,
            "n_pairs_used": self.n_pairs_used,
            "min_g12_observed": self.min_g12_observed,
            "fit": {
                "log_C": self.log_C,
                "fitted_C": self.fitted_C,
                "beta": self.beta,
                "r_squared": self.r_squared,
                "standard_error_beta": self.standard_error_beta,
                "beta_CI_95": [self.beta_ci_95[0], self.beta_ci_95[1]],
                "ci_method": "normal_approx_1.96",
                "decision": self.decision,
            },
        }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path, help="Path to input JSON.")
    parser.add_argument("--output", required=True, type=Path, help="Path to write output JSON.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the output JSON.")
    return parser.parse_args()


def read_json(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except FileNotFoundError as exc:
        raise InputError(f"input file does not exist: {path}") from exc
    except json.JSONDecodeError as exc:
        raise InputError(f"input file is not valid JSON: {path}: {exc}") from exc


def coerce_number(value: Any, *, label: str) -> float:
    if isinstance(value, bool) or value is None:
        raise InputError(f"{label} must be a real number, got {value!r}")
    if isinstance(value, (int, float)):
        number = float(value)
        if not math.isfinite(number):
            raise InputError(f"{label} must be finite, got {value!r}")
        return number
    raise InputError(f"{label} must be a real number, got {type(value).__name__}")


def maybe_number(value: Any) -> float:
    """Best-effort numeric coercion for raw pair rows.

    Calc12 filtering is intentionally tolerant: malformed, non-finite, zero,
    and negative rows count toward n_pairs_raw and are removed before fitting.
    Structural dataset errors still fail closed.
    """

    if isinstance(value, bool) or value is None:
        return math.nan
    if isinstance(value, (int, float)):
        return float(value)
    return math.nan


def is_positive_finite(value: float) -> bool:
    return math.isfinite(value) and value > 0.0


def as_dataset_list(payload: Any) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        raise InputError("top-level input must be a JSON object")
    if "datasets" in payload:
        datasets = payload["datasets"]
        if not isinstance(datasets, list) or not datasets:
            raise InputError("top-level datasets must be a non-empty list")
        result = datasets
    else:
        result = [payload]
    normalized: list[dict[str, Any]] = []
    for index, dataset in enumerate(result):
        if not isinstance(dataset, dict):
            raise InputError(f"dataset {index} must be a JSON object")
        normalized.append(dataset)
    return normalized


def extract_pairs(dataset: dict[str, Any], *, index: int) -> tuple[Any, list[tuple[float, float]]]:
    if "datum_id" not in dataset:
        raise InputError(f"dataset {index} is missing datum_id")
    datum_id = dataset["datum_id"]

    has_pairs = "pairs" in dataset
    has_arrays = "g12" in dataset or "omega_e2_sq" in dataset

    if has_pairs and has_arrays:
        raise InputError(f"dataset {datum_id!r} provides both pairs and array fields; choose one form")
    if has_pairs:
        raw_pairs = dataset["pairs"]
        if not isinstance(raw_pairs, list) or not raw_pairs:
            raise InputError(f"dataset {datum_id!r} pairs must be a non-empty list")
        pairs: list[tuple[float, float]] = []
        for pair_index, pair in enumerate(raw_pairs):
            if isinstance(pair, dict):
                g12 = maybe_number(pair.get("g12"))
                omega = maybe_number(pair.get("omega_e2_sq"))
            elif isinstance(pair, (list, tuple)) and len(pair) == 2:
                g12 = maybe_number(pair[0])
                omega = maybe_number(pair[1])
            else:
                g12 = math.nan
                omega = math.nan
            pairs.append((g12, omega))
        return datum_id, pairs

    if not ("g12" in dataset and "omega_e2_sq" in dataset):
        raise InputError(
            f"dataset {datum_id!r} must provide either pairs or both g12 and omega_e2_sq arrays"
        )

    g12_values = dataset["g12"]
    omega_values = dataset["omega_e2_sq"]
    if not isinstance(g12_values, list) or not isinstance(omega_values, list):
        raise InputError(f"dataset {datum_id!r} g12 and omega_e2_sq must both be lists")
    if len(g12_values) != len(omega_values):
        raise InputError(
            f"dataset {datum_id!r} g12 and omega_e2_sq lengths differ: {len(g12_values)} != {len(omega_values)}"
        )
    if not g12_values:
        raise InputError(f"dataset {datum_id!r} must contain at least one pair")

    pairs = []
    for pair_index, (g12_raw, omega_raw) in enumerate(zip(g12_values, omega_values)):
        g12 = maybe_number(g12_raw)
        omega = maybe_number(omega_raw)
        pairs.append((g12, omega))
    return datum_id, pairs


def fit_power_law(pairs: Iterable[tuple[float, float]]) -> tuple[float, float, float, float, float, tuple[float, float]]:
    xs = [math.log(g12) for g12, _ in pairs]
    ys = [math.log(omega) for _, omega in pairs]
    n = len(xs)
    if n < 3:
        raise InputError(f"at least 3 finite positive pairs are required after filtering; got {n}")

    mean_x = math.fsum(xs) / n
    mean_y = math.fsum(ys) / n
    sxx = math.fsum((x - mean_x) ** 2 for x in xs)
    if sxx <= 0.0:
        raise InputError("g12 values must not all be identical after filtering")
    sxy = math.fsum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    beta = sxy / sxx
    log_C = mean_y - beta * mean_x
    fitted_C = math.exp(log_C)

    residuals = [y - (log_C + beta * x) for x, y in zip(xs, ys)]
    rss = math.fsum(residual ** 2 for residual in residuals)
    tss = math.fsum((y - mean_y) ** 2 for y in ys)
    if tss > 0.0:
        r_squared = max(0.0, min(1.0, 1.0 - rss / tss))
    else:
        r_squared = 1.0 if rss <= 0.0 else 0.0

    if n <= 2:
        raise InputError("standard_error_beta requires at least 3 filtered pairs")
    residual_variance = rss / (n - 2)
    standard_error_beta = math.sqrt(residual_variance / sxx) if residual_variance > 0.0 else 0.0
    beta_ci_95 = (beta - CI_Z_95 * standard_error_beta, beta + CI_Z_95 * standard_error_beta)
    return log_C, fitted_C, beta, r_squared, standard_error_beta, beta_ci_95


def decision_from_ci(beta_ci_95: tuple[float, float]) -> str:
    lower, upper = beta_ci_95
    if lower > 1.0:
        return "regularity_consistent"
    if upper < 1.0:
        return "blowup_precursor"
    return "inconclusive"


def analyze_dataset(dataset: dict[str, Any], *, index: int) -> dict[str, Any]:
    datum_id, raw_pairs = extract_pairs(dataset, index=index)
    n_pairs_raw = len(raw_pairs)
    filtered_pairs = [(g12, omega) for g12, omega in raw_pairs if is_positive_finite(g12) and is_positive_finite(omega)]
    n_pairs_used = len(filtered_pairs)
    if n_pairs_used == 0:
        raise InputError(f"dataset {datum_id!r} has no finite positive pairs after filtering {n_pairs_raw} raw pair(s)")

    log_C, fitted_C, beta, r_squared, standard_error_beta, beta_ci_95 = fit_power_law(filtered_pairs)
    decision = decision_from_ci(beta_ci_95)
    min_g12_observed = min(g12 for g12, _ in filtered_pairs)
    return PairFit(
        datum_id=datum_id,
        n_pairs_raw=n_pairs_raw,
        n_pairs_used=n_pairs_used,
        min_g12_observed=min_g12_observed,
        log_C=log_C,
        fitted_C=fitted_C,
        beta=beta,
        r_squared=r_squared,
        standard_error_beta=standard_error_beta,
        beta_ci_95=beta_ci_95,
        decision=decision,
    ).as_dict()


def aggregate_decision(dataset_decisions: list[str]) -> str:
    if any(decision == "blowup_precursor" for decision in dataset_decisions):
        return "blowup_precursor"
    if dataset_decisions and all(decision == "regularity_consistent" for decision in dataset_decisions):
        return "regularity_consistent"
    return "inconclusive"


def build_payload(input_payload: Any) -> dict[str, Any]:
    datasets = as_dataset_list(input_payload)
    analyzed = [analyze_dataset(dataset, index=index) for index, dataset in enumerate(datasets)]
    decisions = [dataset["fit"]["decision"] for dataset in analyzed]
    return {
        "calc": CALC,
        "route_selector": "statistical",
        "proof_blocking": False,
        "theorem_authority": False,
        "clay_promotion": False,
        "aggregate_decision": aggregate_decision(decisions),
        "datasets": analyzed,
    }


def validate_output(payload: dict[str, Any]) -> None:
    required = {
        "calc",
        "route_selector",
        "proof_blocking",
        "theorem_authority",
        "clay_promotion",
        "aggregate_decision",
        "datasets",
    }
    if not isinstance(payload, dict):
        raise InputError("internal validation failed: output payload must be an object")
    if set(payload) != required:
        missing = sorted(required - set(payload))
        extra = sorted(set(payload) - required)
        raise InputError(f"internal validation failed: output keys mismatch; missing={missing!r} extra={extra!r}")
    if payload["calc"] != CALC:
        raise InputError("internal validation failed: calc must be Calc12")
    if payload["route_selector"] != "statistical":
        raise InputError("internal validation failed: route_selector must be statistical")
    if payload["proof_blocking"] is not False:
        raise InputError("internal validation failed: proof_blocking must be false")
    if payload["theorem_authority"] is not False:
        raise InputError("internal validation failed: theorem_authority must be false")
    if payload["clay_promotion"] is not False:
        raise InputError("internal validation failed: clay_promotion must be false")
    if payload["aggregate_decision"] not in {"regularity_consistent", "blowup_precursor", "inconclusive"}:
        raise InputError(f"internal validation failed: invalid aggregate_decision {payload['aggregate_decision']!r}")
    datasets = payload["datasets"]
    if not isinstance(datasets, list) or not datasets:
        raise InputError("internal validation failed: datasets must be a non-empty list")
    for index, dataset in enumerate(datasets):
        if not isinstance(dataset, dict):
            raise InputError(f"internal validation failed: dataset {index} must be an object")
        if {"datum_id", "n_pairs_raw", "n_pairs_used", "min_g12_observed", "fit"} - set(dataset):
            raise InputError(f"internal validation failed: dataset {index} missing required keys")
        fit = dataset["fit"]
        if not isinstance(fit, dict):
            raise InputError(f"internal validation failed: dataset {index} fit must be an object")
        fit_required = {
            "log_C",
            "fitted_C",
            "beta",
            "r_squared",
            "standard_error_beta",
            "beta_CI_95",
            "ci_method",
            "decision",
        }
        if fit_required - set(fit):
            raise InputError(f"internal validation failed: dataset {index} fit missing required keys")


def write_json(path: Path, value: Any, *, pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if pretty:
        text = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    else:
        text = json.dumps(value, separators=(",", ":"), sort_keys=True, ensure_ascii=False) + "\n"
    path.write_text(text, encoding="utf-8")
    print(text, end="")


def main() -> int:
    args = parse_args()
    try:
        input_payload = read_json(args.input)
        output_payload = build_payload(input_payload)
        validate_output(output_payload)
        write_json(args.output, output_payload, pretty=args.pretty)
    except InputError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
