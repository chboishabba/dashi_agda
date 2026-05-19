#!/usr/bin/env python3
"""Fail-closed W4 Z-peak adequacy harness.

The runner computes the one-parameter adequacy diagnostic only when a caller
supplies an accepted Drell-Yan luminosity convention authority and real per-bin
measurement, dirty-shape prediction, luminosity, and uncertainty inputs.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any

EXIT_USAGE = 64
EXIT_AUTHORITY_MISSING = 40
EXIT_INPUT_MISSING = 41
EXIT_PARSE_ERROR = 42
EXIT_COMPUTE_ERROR = 43

RESULT_ADEQUATE = "adequate"
RESULT_OBSTRUCTED = "obstructed"
RESULT_THRESHOLD_MISSING = "threshold-missing"

FAIL_TYPE_THRESHOLD_EXCEEDED = "thresholdExceeded"
FAIL_TYPE_THRESHOLD_MISSING = "typedReviewThresholdMissing"
FAIL_CAUSE_EXTRACTION_CONVENTION_MISMATCH = "likelyExtractionOrConventionMismatch"
FAIL_CAUSE_THRESHOLD_NOT_AUTHORITY_BACKED = "thresholdNotAuthorityBacked"

REQUIRED_AUTHORITY_FIELDS = (
    "status",
    "pdfSet",
    "lhapdfId",
    "gridChecksum",
    "scaleConvention",
    "rapidityConvention",
    "massBinRule",
    "flavourWeights",
    "interpolationIntegration",
    "source",
    "provenance",
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_authority(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ValueError(f"authority file is unreadable: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"authority file is not valid JSON: {exc}") from exc

    missing = [field for field in REQUIRED_AUTHORITY_FIELDS if field not in payload]
    if missing:
        raise ValueError(f"authority file is missing required fields: {', '.join(missing)}")
    if payload["status"] not in ("accepted", "replacement"):
        raise ValueError("authority status must be 'accepted' or 'replacement'")
    return payload


def read_numeric_csv(path: Path, value_column: str, *, label: str) -> list[float]:
    try:
        handle = path.open("r", encoding="utf-8", newline="")
    except OSError as exc:
        raise ValueError(f"{label} CSV is unreadable: {exc}") from exc

    with handle:
        reader: csv.DictReader[str] | None = None
        for raw_line in handle:
            if raw_line.startswith("#") or not raw_line.strip():
                continue
            reader = csv.DictReader([raw_line, *handle])
            break

        if reader is None or reader.fieldnames is None:
            raise ValueError(f"{label} CSV has no header")
        if value_column not in reader.fieldnames:
            raise ValueError(
                f"{label} CSV missing column {value_column!r}; available columns: {reader.fieldnames!r}"
            )

        values: list[float] = []
        for row_index, row in enumerate(reader):
            raw = row.get(value_column)
            if raw is None or raw == "":
                raise ValueError(f"{label} row {row_index} has empty {value_column!r}")
            try:
                value = float(raw)
            except ValueError as exc:
                raise ValueError(f"{label} row {row_index} has non-numeric value {raw!r}") from exc
            if not math.isfinite(value):
                raise ValueError(f"{label} row {row_index} has non-finite value {raw!r}")
            values.append(value)

    if not values:
        raise ValueError(f"{label} CSV has no data rows")
    return values


def compute_adequacy(
    measurement: list[float],
    prediction_shape: list[float],
    luminosity: list[float],
    sigma: list[float],
) -> dict[str, Any]:
    lengths = {len(measurement), len(prediction_shape), len(luminosity), len(sigma)}
    if len(lengths) != 1:
        raise ValueError(
            "input vector lengths differ: "
            f"measurement={len(measurement)}, prediction={len(prediction_shape)}, "
            f"luminosity={len(luminosity)}, sigma={len(sigma)}"
        )
    if not measurement:
        raise ValueError("input vectors are empty")
    if any(value <= 0.0 for value in sigma):
        raise ValueError("all sigma values must be positive")

    weighted_shape = [d_i * ell_i for d_i, ell_i in zip(prediction_shape, luminosity, strict=True)]
    numerator = sum(
        m_i * x_i / (sigma_i * sigma_i)
        for m_i, x_i, sigma_i in zip(measurement, weighted_shape, sigma, strict=True)
    )
    denominator = sum(
        x_i * x_i / (sigma_i * sigma_i)
        for x_i, sigma_i in zip(weighted_shape, sigma, strict=True)
    )
    if denominator <= 0.0 or not math.isfinite(denominator):
        raise ValueError("alpha denominator is non-positive or non-finite")

    alpha = numerator / denominator
    residuals = [
        m_i - alpha * x_i
        for m_i, x_i in zip(measurement, weighted_shape, strict=True)
    ]
    pulls = [
        residual / sigma_i
        for residual, sigma_i in zip(residuals, sigma, strict=True)
    ]
    chi2 = sum(pull * pull for pull in pulls)
    dof = max(len(measurement) - 1, 1)
    return {
        "alphaStar": alpha,
        "chi2": chi2,
        "dof": dof,
        "chi2PerDof": chi2 / dof,
        "rowCount": len(measurement),
        "formula": "chi2(alpha)=sum((m_i-alpha d_i ell_i)^2/sigma_i^2); alpha*=sum(m_i d_i ell_i/sigma_i^2)/sum((d_i ell_i)^2/sigma_i^2)",
        "perBin": [
            {
                "index": index,
                "measurement": measurement[index],
                "predictionShape": prediction_shape[index],
                "luminosity": luminosity[index],
                "sigma": sigma[index],
                "scaledPrediction": alpha * weighted_shape[index],
                "residual": residuals[index],
                "pull": pulls[index],
            }
            for index in range(len(measurement))
        ],
    }


def stable_digest(payload: dict[str, Any]) -> str:
    stable = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(stable.encode("utf-8")).hexdigest()


def classify_result(chi2_per_dof: float, threshold: float | None) -> dict[str, Any]:
    if threshold is None:
        return {
            "kind": RESULT_THRESHOLD_MISSING,
            "adequate": None,
            "failType": FAIL_TYPE_THRESHOLD_MISSING,
            "failCause": FAIL_CAUSE_THRESHOLD_NOT_AUTHORITY_BACKED,
            "review": "supply a typed adequacy threshold before classifying pass/fail",
        }
    if chi2_per_dof <= threshold:
        return {
            "kind": RESULT_ADEQUATE,
            "adequate": True,
            "failType": None,
            "failCause": None,
            "review": "numeric adequacy under supplied threshold; still no W4 promotion",
        }
    return {
        "kind": RESULT_OBSTRUCTED,
        "adequate": False,
        "failType": FAIL_TYPE_THRESHOLD_EXCEEDED,
        "failCause": FAIL_CAUSE_EXTRACTION_CONVENTION_MISMATCH,
        "review": (
            "chi2/dof exceeds supplied threshold; likely extraction/convention mismatch "
            "until accepted DY convention and aligned inputs are rerun"
        ),
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run gated W4 Z-peak adequacy calculation.")
    parser.add_argument("--accepted-dy-authority", type=Path, required=True)
    parser.add_argument("--measurement-csv", type=Path, required=True)
    parser.add_argument("--measurement-column", required=True)
    parser.add_argument("--prediction-csv", type=Path, required=True)
    parser.add_argument("--prediction-column", required=True)
    parser.add_argument("--luminosity-csv", type=Path, required=True)
    parser.add_argument("--luminosity-column", required=True)
    parser.add_argument("--sigma-csv", type=Path, required=True)
    parser.add_argument("--sigma-column", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--adequacy-threshold", type=float, default=None)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        authority = load_authority(args.accepted_dy_authority)
    except ValueError as exc:
        print(f"blocked: missing accepted DY luminosity convention authority: {exc}", file=sys.stderr)
        return EXIT_AUTHORITY_MISSING

    paths = [
        args.measurement_csv,
        args.prediction_csv,
        args.luminosity_csv,
        args.sigma_csv,
    ]
    missing_paths = [str(path) for path in paths if not path.exists()]
    if missing_paths:
        print(f"blocked: missing required input files: {', '.join(missing_paths)}", file=sys.stderr)
        return EXIT_INPUT_MISSING

    try:
        measurement = read_numeric_csv(args.measurement_csv, args.measurement_column, label="measurement")
        prediction = read_numeric_csv(args.prediction_csv, args.prediction_column, label="prediction")
        luminosity = read_numeric_csv(args.luminosity_csv, args.luminosity_column, label="luminosity")
        sigma = read_numeric_csv(args.sigma_csv, args.sigma_column, label="sigma")
    except ValueError as exc:
        print(f"blocked: input parse failed: {exc}", file=sys.stderr)
        return EXIT_PARSE_ERROR

    try:
        calculation = compute_adequacy(measurement, prediction, luminosity, sigma)
    except ValueError as exc:
        print(f"blocked: adequacy calculation failed: {exc}", file=sys.stderr)
        return EXIT_COMPUTE_ERROR

    threshold = args.adequacy_threshold
    result = classify_result(calculation["chi2PerDof"], threshold)
    artifact: dict[str, Any] = {
        "artifactSchema": "dashi-w4-z-peak-adequacy-v1",
        "schemaVersion": "0.2.0",
        "status": "computed-not-promoted",
        "authorityStatus": authority["status"],
        "sourceAuthority": {
            "record": "ins2079374",
            "measurementTableDoi": "10.17182/hepdata.115656.v1/t21",
            "massWindow": "76-106 GeV",
        },
        "inputDigests": {
            "acceptedDYLuminosityConventionAuthority": sha256_file(args.accepted_dy_authority),
            "measurementCsv": sha256_file(args.measurement_csv),
            "predictionCsv": sha256_file(args.prediction_csv),
            "luminosityCsv": sha256_file(args.luminosity_csv),
            "sigmaCsv": sha256_file(args.sigma_csv),
        },
        "columns": {
            "measurement": args.measurement_column,
            "prediction": args.prediction_column,
            "luminosity": args.luminosity_column,
            "sigma": args.sigma_column,
        },
        "acceptedAuthoritySummary": {
            field: authority[field]
            for field in REQUIRED_AUTHORITY_FIELDS
            if field != "provenance"
        },
        "calculation": calculation,
        "adequacyThreshold": threshold,
        "adequacyDecision": result["adequate"],
        "result": result,
        "promotionBoundary": [
            "no W4 promotion",
            "no Candidate256 physical calibration authority",
            "negative adequacy results remain visible as typed obstructions",
            "no adequacy claim without downstream typed receipt review",
        ],
    }
    artifact["artifactDigest"] = stable_digest(artifact)
    write_json(args.output, artifact)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
