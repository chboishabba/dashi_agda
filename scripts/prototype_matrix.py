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
    parser = argparse.ArgumentParser(description="Build a small prototype prediction matrix")
    parser.add_argument(
        "--state",
        action="append",
        required=True,
        help="Path to a state.json file. Pass more than once for a batch matrix.",
    )
    parser.add_argument("--config", help="Optional .json/.yaml config file")
    parser.add_argument("--output", help="Optional output path; defaults to stdout")
    return parser.parse_args()


def make_gbw_params(config: RunnerConfig) -> GBWParameters:
    return GBWParameters(
        lambda_gbw=config.lambda_gbw,
        x0=config.x0,
        sigma0=config.sigma0,
        thickness=config.thickness,
        normalization_d0=config.normalization_d0,
        sqrt_s=config.sqrt_s,
        defect_floor=config.defect_floor,
    )


def make_ipsat_params(config: RunnerConfig) -> IPsatParameters:
    return IPsatParameters(
        lambda_ipsat=config.lambda_gbw,
        x0=config.x0,
        sigma0=config.sigma0,
        alpha_s=0.2,
        thickness=config.thickness,
        normalization_d0=config.normalization_d0,
        sqrt_s=config.sqrt_s,
        defect_floor=config.defect_floor,
    )


def main() -> None:
    args = parse_args()
    config = load_config(Path(args.config)) if args.config else RunnerConfig()
    gbw_params = make_gbw_params(config)
    ipsat_params = make_ipsat_params(config)

    rows = []
    for state_path in args.state:
        state = _load_json(ensure_canonical_example(Path(state_path)))
        obs = extract_observables(state, config)
        gbw = gbw_response(obs, gbw_params)
        ipsat = ipsat_response(obs, ipsat_params)
        rows.append(
            {
                "trace_id": obs.trace_id,
                "observables": asdict(obs),
                "models": {
                    "gbw": {
                        "response": asdict(gbw),
                        "scorecard": asdict(
                            score_explanation(
                                obs,
                                residual=gbw.residual,
                                confidence=gbw.confidence,
                            )
                        ),
                    },
                    "ipsat": {
                        "response": asdict(ipsat),
                        "scorecard": asdict(
                            score_explanation(
                                obs,
                                residual=ipsat.residual,
                                confidence=ipsat.confidence,
                            )
                        ),
                    },
                },
                "model_gap": {
                    "predicted_yield_gap": gbw.predicted_yield - ipsat.predicted_yield,
                    "residual_gap": gbw.residual - ipsat.residual,
                    "explanation_cost_gap": (
                        score_explanation(obs, residual=gbw.residual, confidence=gbw.confidence).explanation_cost
                        - score_explanation(obs, residual=ipsat.residual, confidence=ipsat.confidence).explanation_cost
                    ),
                },
            }
        )

    payload = {
        "matrix_type": "prototype-explanation-matrix",
        "notes": [
            "This artifact compares explanatory decompositions across channels and model families.",
            "It is surrogate-only and does not perform fitting or empirical validation.",
            "Interpret differences as changes in explanation under fixed Dashi-derived observables or fixed model assumptions."
        ],
        "rows": rows,
    }

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(encoded, encoding="utf-8")
    else:
        print(encoded)


if __name__ == "__main__":
    main()
