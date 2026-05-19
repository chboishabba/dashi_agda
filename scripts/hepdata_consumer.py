#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

try:
    from prototype_schema import MeasurementSurface, load_measurement_surface
except ModuleNotFoundError:
    from scripts.prototype_schema import MeasurementSurface, load_measurement_surface


def load_hepdata_artifact(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        artifact = json.load(handle)

    if not isinstance(artifact, dict):
        raise ValueError("artifact must decode to a JSON object")
    if artifact.get("artifact_schema") != "dashi-hpdata-empirical-v1":
        raise ValueError("unsupported artifact_schema")
    if artifact.get("schema_version") != "1.0.0":
        raise ValueError("unsupported schema_version")
    return artifact


def select_family_artifact(
    artifact: dict[str, Any],
    family: str | None = None,
) -> dict[str, Any]:
    if "family" in artifact:
        payload = artifact["family"]
        if family is not None and payload.get("family") != family:
            raise ValueError(
                f"artifact contains family '{payload.get('family')}', not '{family}'"
            )
        if not isinstance(payload, dict):
            raise ValueError("artifact.family must be a JSON object")
        return payload

    families = artifact.get("families")
    if not isinstance(families, dict):
        raise ValueError("artifact must contain either 'family' or 'families'")
    if family is None:
        raise ValueError("family is required when artifact contains multiple families")
    payload = families.get(family)
    if not isinstance(payload, dict):
        raise ValueError(f"family '{family}' not present in artifact")
    return payload


def to_measurement_surface(
    artifact: dict[str, Any],
    *,
    family: str | None = None,
) -> MeasurementSurface:
    family_payload = select_family_artifact(artifact, family)
    validation_summary = family_payload.get("validation_summary", {})
    if not isinstance(validation_summary, dict):
        raise ValueError("family validation_summary must be a JSON object")
    validation_status = validation_summary.get("validation_status")
    if validation_status != "empirical-artifact-ready":
        raise ValueError(
            "artifact family is not ready for measurement-surface consumption: "
            f"{validation_status!r}"
        )

    family_name = str(family_payload.get("family", family or "anonymous-family"))
    measurement = family_payload.get("measurement")
    if not isinstance(measurement, dict):
        raise ValueError("family measurement payload must be a JSON object")
    return load_measurement_surface(measurement, trace_id=family_name)


def build_summary(
    artifact: dict[str, Any],
    surface: MeasurementSurface,
    *,
    family: str | None = None,
) -> dict[str, Any]:
    family_payload = select_family_artifact(artifact, family)
    measurement = family_payload["measurement"]
    validation_summary = family_payload["validation_summary"]
    evidence_summary = family_payload.get("evidence_summary", {})
    return {
        "trace_id": surface.trace_id,
        "point_count": len(surface.x),
        "covariance_shape": [len(surface.cov), len(surface.cov[0]) if surface.cov else 0],
        "measurement_path": measurement.get("path"),
        "measurement_kind": measurement.get("kind"),
        "measurement_field_status": measurement.get("field_status", {}),
        "validation_status": validation_summary.get("validation_status"),
        "counts": evidence_summary.get("counts", {}),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Consume a canonical HEPData empirical artifact and extract only the "
            "validated measurement surface."
        )
    )
    parser.add_argument("artifact", help="Path to canonical artifact JSON")
    parser.add_argument("--family", help="Family name when the artifact contains multiple families")
    parser.add_argument(
        "--output",
        help="Optional output path. Defaults to stdout.",
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="Emit a compact summary instead of the full measurement surface payload.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    artifact = load_hepdata_artifact(Path(args.artifact))
    surface = to_measurement_surface(artifact, family=args.family)
    payload = build_summary(artifact, surface, family=args.family)
    if not args.summary_only:
        payload["measurement_surface"] = asdict(surface)

    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
