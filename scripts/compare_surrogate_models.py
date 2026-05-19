#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from pathlib import Path

from emit_shift_prototype_examples import ensure_canonical_example
from prototype_gbw import GBWParameters, gbw_response
from prototype_ipsat import IPsatParameters, ipsat_response
from prototype_scorecard import score_explanation
from prototype_runner import RunnerConfig, extract_observables, load_config, _load_json


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Compare GBW- and IPsat-style surrogate explanations")
    parser.add_argument("--state", required=True, help="Path to state.json")
    parser.add_argument("--config", help="Optional .json/.yaml config file")
    parser.add_argument("--output", help="Optional output path; defaults to stdout")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    config = load_config(Path(args.config)) if args.config else RunnerConfig()
    state = _load_json(ensure_canonical_example(Path(args.state)))
    observables = extract_observables(state, config)

    gbw = gbw_response(
        observables,
        GBWParameters(
            lambda_gbw=config.lambda_gbw,
            x0=config.x0,
            sigma0=config.sigma0,
            thickness=config.thickness,
            normalization_d0=config.normalization_d0,
            sqrt_s=config.sqrt_s,
            defect_floor=config.defect_floor,
        ),
    )

    ipsat = ipsat_response(
        observables,
        IPsatParameters(
            lambda_ipsat=config.lambda_gbw,
            x0=config.x0,
            sigma0=config.sigma0,
            alpha_s=0.2,
            thickness=config.thickness,
            normalization_d0=config.normalization_d0,
            sqrt_s=config.sqrt_s,
            defect_floor=config.defect_floor,
        ),
    )

    gbw_score = score_explanation(
        observables,
        residual=gbw.residual,
        confidence=gbw.confidence,
    )
    ipsat_score = score_explanation(
        observables,
        residual=ipsat.residual,
        confidence=ipsat.confidence,
    )

    payload = {
        "trace_id": observables.trace_id,
        "observables": asdict(observables),
        "gbw": {
            "response": asdict(gbw),
            "scorecard": asdict(gbw_score),
        },
        "ipsat": {
            "response": asdict(ipsat),
            "scorecard": asdict(ipsat_score),
        },
        "comparison": {
            "predicted_yield_gap": gbw.predicted_yield - ipsat.predicted_yield,
            "residual_gap": gbw.residual - ipsat.residual,
            "explanation_cost_gap": gbw_score.explanation_cost - ipsat_score.explanation_cost,
            "interpretation": [
                "This compares surrogate-model explanations on the same Dashi-derived observables.",
                "It does not determine which model is physically correct.",
                "Lower explanation cost means the surrogate explains the same observables more efficiently under the shared non-fitting scorecard.",
                "Use the gap to inspect sensitivity of the explanation to model assumptions."
            ],
        },
    }

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(encoded, encoding="utf-8")
    else:
        print(encoded)


if __name__ == "__main__":
    main()
