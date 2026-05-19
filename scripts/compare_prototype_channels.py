#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

from emit_shift_prototype_examples import ensure_canonical_example
from prototype_gbw import GBWParameters, gbw_response
from prototype_scorecard import score_explanation
from prototype_schema import NumericObservables
from prototype_runner import RunnerConfig, build_output, extract_observables, load_config, _load_json


def _load_state(path: Path) -> dict[str, Any]:
    return _load_json(path)


def _explanation_summary(result: dict[str, Any]) -> dict[str, Any]:
    obs = result["observables"]
    response = result["response"]
    observables = NumericObservables(**obs)
    score = score_explanation(
        observables,
        residual=response["residual"],
        confidence=response["confidence"],
    )
    return {
        "trace_id": result["trace_id"],
        "delta_defect": obs["delta_defect"],
        "mdl_level": obs["mdl_level"],
        "promoted_d0": obs["promoted_d0"],
        "g_star": obs["g_star"],
        "q_s": obs["q_s"],
        "predicted_yield": result["predicted_yield"],
        "residual": response["residual"],
        "confidence": response["confidence"],
        "scorecard": asdict(score),
    }


def _compare(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    l_obs = left["observables"]
    r_obs = right["observables"]
    l_resp = left["response"]
    r_resp = right["response"]

    return {
        "left_trace": left["trace_id"],
        "right_trace": right["trace_id"],
        "delta_defect_gap": l_obs["delta_defect"] - r_obs["delta_defect"],
        "mdl_gap": l_obs["mdl_level"] - r_obs["mdl_level"],
        "promoted_d0_gap": l_obs["promoted_d0"] - r_obs["promoted_d0"],
        "g_star_gap": l_obs["g_star"] - r_obs["g_star"],
        "q_s_gap": l_obs["q_s"] - r_obs["q_s"],
        "predicted_yield_gap": left["predicted_yield"] - right["predicted_yield"],
        "residual_gap": l_resp["residual"] - r_resp["residual"],
        "explanation_cost_gap": left["summary"]["scorecard"]["explanation_cost"] - right["summary"]["scorecard"]["explanation_cost"],
        "interpretation": [
            "This output compares explanatory factors, not empirical truth.",
            "Positive gaps mean the left channel carries more of that surrogate quantity.",
            "Lower explanation cost means the surrogate explains that channel more efficiently under its internal, non-fitting scorecard.",
            "Use this to inspect whether the prototype attributes cleaner explanation to boundary/defect structure rather than asserting a fixed ranking law."
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Compare two prototype channel explanations")
    parser.add_argument("--left", required=True, help="Path to first state.json")
    parser.add_argument("--right", required=True, help="Path to second state.json")
    parser.add_argument("--config", help="Optional .json/.yaml config file")
    parser.add_argument("--output", help="Optional output path; defaults to stdout")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    config = load_config(Path(args.config)) if args.config else RunnerConfig()
    params = GBWParameters(
        lambda_gbw=config.lambda_gbw,
        x0=config.x0,
        sigma0=config.sigma0,
        thickness=config.thickness,
        normalization_d0=config.normalization_d0,
        sqrt_s=config.sqrt_s,
        defect_floor=config.defect_floor,
    )

    left_state = _load_state(ensure_canonical_example(Path(args.left)))
    right_state = _load_state(ensure_canonical_example(Path(args.right)))

    left_obs = extract_observables(left_state, config)
    right_obs = extract_observables(right_state, config)
    left_result = build_output(left_obs, gbw_response(left_obs, params))
    right_result = build_output(right_obs, gbw_response(right_obs, params))

    left_summary = _explanation_summary(left_result)
    right_summary = _explanation_summary(right_result)
    payload = {
        "left": left_summary,
        "right": right_summary,
        "comparison": _compare(
            {"trace_id": left_result["trace_id"], "predicted_yield": left_result["predicted_yield"], "observables": left_result["observables"], "response": left_result["response"], "summary": left_summary},
            {"trace_id": right_result["trace_id"], "predicted_yield": right_result["predicted_yield"], "observables": right_result["observables"], "response": right_result["response"], "summary": right_summary},
        ),
    }

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(encoded, encoding="utf-8")
    else:
        print(encoded)


if __name__ == "__main__":
    main()
