#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

try:
    from hepdata_consumer import load_hepdata_artifact
    from hepdata_projection_contract import projection_contract_summary
    from hepdata_surface_report import build_surface_report
except ModuleNotFoundError:
    from scripts.hepdata_consumer import load_hepdata_artifact
    from scripts.hepdata_projection_contract import projection_contract_summary
    from scripts.hepdata_surface_report import build_surface_report


PROGRAM_SURFACE_LABEL = "hepdata-empirical-program-surface"
PROGRAM_STATUS = "empirical-program-surface"
PROGRAM_CLAIM_BOUNDARY = (
    "Packaging only. This surface names the validated measurement/report path "
    "without implementing MeasurementSurface -> DashiStateSchema projection "
    "and without making theorem claims."
)


def build_program_surface(
    artifact: dict[str, Any],
    *,
    family: str | None = None,
) -> dict[str, Any]:
    surface_report = build_surface_report(artifact, family=family)
    measurement_summary = surface_report["measurement_summary"]

    return {
        "program_surface_label": PROGRAM_SURFACE_LABEL,
        "program_status": PROGRAM_STATUS,
        "claim_boundary": PROGRAM_CLAIM_BOUNDARY,
        "family": family or measurement_summary["trace_id"],
        "measurement_summary": measurement_summary,
        "surface_report": surface_report,
        "projection_contract": projection_contract_summary(),
        "gates": {
            "measurement_ready": bool(surface_report["metric_ready"]),
            "projection_eligible": bool(surface_report["projection_eligible"]),
            "surface_validation": surface_report["surface_validation"],
            "validation_status": measurement_summary["validation_status"],
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Promote one validated HEPData measurement/report path into the "
            "named repo-facing empirical program surface."
        )
    )
    parser.add_argument("artifact", help="Path to canonical artifact JSON")
    parser.add_argument("--family", help="Family name when the artifact contains multiple families")
    parser.add_argument("--output", help="Optional output path. Defaults to stdout.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    artifact = load_hepdata_artifact(Path(args.artifact))
    payload = build_program_surface(artifact, family=args.family)
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
