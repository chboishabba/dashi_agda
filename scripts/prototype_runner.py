#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from prototype_gbw import GBWParameters, gbw_response, GBWResponse
from prototype_schema import NumericObservables, extract_numeric_observables, load_state_schema


@dataclass
class RunnerConfig:
    lambda_gbw: float = 0.3
    x0: float = 1.0e-3
    sigma0: float = 1.0
    thickness: float = 1.0
    normalization_d0: float = 1.0
    sqrt_s: float = 1.0
    alpha_qs: float = 0.5
    mdl_lambda: float = 1.0
    defect_floor: float = 1.0e-9


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError("state/config file must decode to a JSON object")
    return data


def load_config(path: Path | None) -> RunnerConfig:
    if path is None:
        return RunnerConfig()

    suffix = path.suffix.lower()
    if suffix == ".json":
        raw = _load_json(path)
    elif suffix in {".yaml", ".yml"}:
        try:
            import yaml  # type: ignore
        except ImportError as exc:
            raise RuntimeError("YAML config requested but PyYAML is not installed") from exc
        with path.open("r", encoding="utf-8") as handle:
            raw = yaml.safe_load(handle) or {}
        if not isinstance(raw, dict):
            raise ValueError("YAML config must decode to a mapping")
    else:
        raise ValueError("config must be .json, .yaml, or .yml")

    allowed = {field.name for field in RunnerConfig.__dataclass_fields__.values()}
    filtered = {key: value for key, value in raw.items() if key in allowed}
    return RunnerConfig(**filtered)


def extract_observables(state: dict[str, Any], config: RunnerConfig) -> NumericObservables:
    schema = load_state_schema(state)
    return extract_numeric_observables(
        schema,
        mdl_lambda=config.mdl_lambda,
        alpha_qs=config.alpha_qs,
    )


def build_output(obs: NumericObservables, response: GBWResponse) -> dict[str, Any]:
    return {
        "trace_id": obs.trace_id,
        "predicted_yield": response.predicted_yield,
        "flags": {
            "confidence": response.confidence,
            "surrogate_only": True,
            "fit_performed": False,
        },
        "observables": asdict(obs),
        "response": asdict(response),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Reduced Dashi photonuclear prototype runner")
    parser.add_argument("--state", required=True, help="Path to state.json input")
    parser.add_argument("--config", help="Optional .json/.yaml config file")
    parser.add_argument("--output", help="Optional output path; defaults to stdout")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    state = _load_json(Path(args.state))
    config = load_config(Path(args.config)) if args.config else RunnerConfig()

    observables = extract_observables(state, config)
    response = gbw_response(
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
    output = build_output(observables, response)

    if args.output:
        output_path = Path(args.output)
        output_path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
