#!/usr/bin/env python3
"""Emit a deterministic Calc 12 result ledger from the real route selector."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


CONTRACT = "ns_clay_calc12_result_ledger"
VERSION = 1
DEFAULT_INPUT = Path("scripts") / "data" / "outputs" / "ns_clay_calc12_route_selector_real_N128_20260619.json"
DEFAULT_OUTPUT = Path("outputs") / f"{CONTRACT}.json"

CONTROL_CARD = {
    "O": "Worker 1 owns the Calc 12 result ledger emitter and its focused test.",
    "R": (
        "Record the real Calc 12 selector result, keep proof/theorem/Clay "
        "promotion false, and emit a deterministic JSON ledger."
    ),
    "C": "A stdlib-only Python CLI reads one selector artifact, validates it, and writes canonical JSON.",
    "S": "The input is a real route-selector output, not a proof certificate.",
    "L": "input artifact -> validation -> extracted beta/CI/r_squared/n_pairs_used/decision -> ledger.",
    "P": "Use the ledger as a non-promoting receipt for the Calc 12 selector result.",
    "G": "Validation passes only when the expected route-selector shape is present and all promotion flags are false.",
    "F": "The ledger explicitly records proof_blocking False, theorem_authority False, and clay_promotion False.",
}

REQUIRED_TOP_LEVEL_KEYS = {
    "calc",
    "route_selector",
    "proof_blocking",
    "theorem_authority",
    "clay_promotion",
    "aggregate_decision",
    "datasets",
}

REQUIRED_FIT_KEYS = {
    "beta",
    "beta_CI_95",
    "r_squared",
    "decision",
}


class InputError(ValueError):
    """Raised when the input JSON does not match the result-ledger contract."""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="Path to the route selector JSON.")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Path to write the ledger JSON.")
    return parser.parse_args()


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise InputError(f"input file does not exist: {path}") from exc
    except json.JSONDecodeError as exc:
        raise InputError(f"input file is not valid JSON: {path}: {exc}") from exc


def _coerce_ci(value: Any) -> list[float]:
    if not isinstance(value, list) or len(value) != 2:
        raise InputError("beta_CI_95 must be a two-item list")
    lower, upper = value
    for index, entry in enumerate((lower, upper)):
        if isinstance(entry, bool) or not isinstance(entry, (int, float)):
            raise InputError(f"beta_CI_95[{index}] must be a real number")
    lower_f = float(lower)
    upper_f = float(upper)
    if lower_f > upper_f:
        raise InputError("beta_CI_95 lower bound must not exceed upper bound")
    return [lower_f, upper_f]


def validate_input_payload(payload: Any) -> None:
    if not isinstance(payload, dict):
        raise InputError("top-level input must be a JSON object")
    missing = REQUIRED_TOP_LEVEL_KEYS - set(payload)
    extra = set(payload) - REQUIRED_TOP_LEVEL_KEYS
    if missing or extra:
        raise InputError(
            f"top-level route selector keys mismatch; missing={sorted(missing)!r} extra={sorted(extra)!r}"
        )
    if payload.get("calc") != "Calc12":
        raise InputError("calc must be Calc12")
    if payload.get("route_selector") != "statistical":
        raise InputError("route_selector must be statistical")
    if payload.get("proof_blocking") is not False:
        raise InputError("proof_blocking must be false")
    if payload.get("theorem_authority") is not False:
        raise InputError("theorem_authority must be false")
    if payload.get("clay_promotion") is not False:
        raise InputError("clay_promotion must be false")
    if payload.get("aggregate_decision") not in {
        "regularity_consistent",
        "blowup_precursor",
        "inconclusive",
    }:
        raise InputError(f"invalid aggregate_decision {payload.get('aggregate_decision')!r}")

    datasets = payload.get("datasets")
    if not isinstance(datasets, list) or len(datasets) != 1:
        raise InputError("datasets must be a one-item list")

    dataset = datasets[0]
    if not isinstance(dataset, dict):
        raise InputError("dataset 0 must be a JSON object")
    required_dataset_keys = {"datum_id", "fit", "n_pairs_raw", "n_pairs_used", "min_g12_observed"}
    missing_dataset = required_dataset_keys - set(dataset)
    extra_dataset = set(dataset) - required_dataset_keys
    if missing_dataset or extra_dataset:
        raise InputError(
            f"dataset 0 keys mismatch; missing={sorted(missing_dataset)!r} extra={sorted(extra_dataset)!r}"
        )

    n_pairs_used = dataset.get("n_pairs_used")
    if isinstance(n_pairs_used, bool) or not isinstance(n_pairs_used, int) or n_pairs_used <= 0:
        raise InputError("n_pairs_used must be a positive integer")

    fit = dataset.get("fit")
    if not isinstance(fit, dict):
        raise InputError("dataset 0 fit must be a JSON object")
    missing_fit = REQUIRED_FIT_KEYS - set(fit)
    extra_fit = set(fit) - (REQUIRED_FIT_KEYS | {"ci_method", "fitted_C", "log_C", "standard_error_beta"})
    if missing_fit or extra_fit:
        raise InputError(f"dataset 0 fit keys mismatch; missing={sorted(missing_fit)!r} extra={sorted(extra_fit)!r}")

    beta = fit.get("beta")
    r_squared = fit.get("r_squared")
    if isinstance(beta, bool) or not isinstance(beta, (int, float)):
        raise InputError("beta must be a real number")
    if isinstance(r_squared, bool) or not isinstance(r_squared, (int, float)):
        raise InputError("r_squared must be a real number")
    r_squared_f = float(r_squared)
    if not 0.0 <= r_squared_f <= 1.0:
        raise InputError("r_squared must lie in [0, 1]")

    _coerce_ci(fit.get("beta_CI_95"))


def build_payload(input_payload: Any, *, input_path: Path) -> dict[str, Any]:
    validate_input_payload(input_payload)
    dataset = input_payload["datasets"][0]
    fit = dataset["fit"]
    ci = _coerce_ci(fit["beta_CI_95"])
    return {
        "contract": CONTRACT,
        "version": VERSION,
        "input": str(input_path),
        "control_card": dict(CONTROL_CARD),
        "result": {
            "aggregate_decision": input_payload["aggregate_decision"],
            "beta": float(fit["beta"]),
            "ci": ci,
            "n_pairs_used": int(dataset["n_pairs_used"]),
            "r_squared": float(fit["r_squared"]),
        },
        "proof_blocking": False,
        "theorem_authority": False,
        "clay_promotion": False,
        "validation_passed": False,
    }


def validate_payload(payload: Any) -> bool:
    if not isinstance(payload, dict):
        return False
    required_keys = {
        "contract",
        "version",
        "input",
        "control_card",
        "result",
        "proof_blocking",
        "theorem_authority",
        "clay_promotion",
        "validation_passed",
    }
    if set(payload) != required_keys:
        return False
    if payload.get("contract") != CONTRACT:
        return False
    if payload.get("version") != VERSION:
        return False
    if not isinstance(payload.get("input"), str) or not payload["input"]:
        return False

    control_card = payload.get("control_card")
    if not isinstance(control_card, dict) or set(control_card) != set(CONTROL_CARD):
        return False
    if control_card != CONTROL_CARD:
        return False

    result = payload.get("result")
    if not isinstance(result, dict):
        return False
    if set(result) != {"aggregate_decision", "beta", "ci", "n_pairs_used", "r_squared"}:
        return False
    if result["aggregate_decision"] not in {"regularity_consistent", "blowup_precursor", "inconclusive"}:
        return False
    if isinstance(result["beta"], bool) or not isinstance(result["beta"], (int, float)):
        return False
    if not isinstance(result["ci"], list) or len(result["ci"]) != 2:
        return False
    if any(isinstance(value, bool) or not isinstance(value, (int, float)) for value in result["ci"]):
        return False
    if isinstance(result["n_pairs_used"], bool) or not isinstance(result["n_pairs_used"], int):
        return False
    if isinstance(result["r_squared"], bool) or not isinstance(result["r_squared"], (int, float)):
        return False
    r_squared = float(result["r_squared"])
    if not 0.0 <= r_squared <= 1.0:
        return False

    if payload.get("proof_blocking") is not False:
        return False
    if payload.get("theorem_authority") is not False:
        return False
    if payload.get("clay_promotion") is not False:
        return False
    if payload.get("validation_passed") is not True:
        return False
    return True


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    path.write_text(text, encoding="utf-8")
    print(text, end="")


def main() -> int:
    args = parse_args()
    try:
        input_payload = read_json(args.input)
        payload = build_payload(input_payload, input_path=args.input)
        payload["validation_passed"] = validate_payload({**payload, "validation_passed": True})
        if not validate_payload(payload):
            raise InputError("internal validation failed")
        write_json(args.output, payload)
    except InputError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
