#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
from typing import Any


DEFAULT_STRICT_ARTIFACT = Path("scripts/data/outputs/t43_strict_log_sigma_dashi_v4_20260515.json")
DEFAULT_OUTPUT = Path("scripts/data/outputs/emst_wi_provider_contract_20260516.json")
Z_MASS_GEV = 91.1876
W_COLUMNS = [f"W{index}" for index in range(9)]
REQUIRED_COLUMNS = ["phi_star", "qT_GeV", *W_COLUMNS]


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _strict_grid(strict_artifact: dict[str, Any]) -> list[dict[str, float]]:
    rows = []
    for item in strict_artifact["per_bin"]:
        phi_star = float(item["phiStar"])
        rows.append(
            {
                "bin": int(item["bin"]),
                "phi_star": phi_star,
                "phi_star_low": float(item["phiStarLow"]),
                "phi_star_high": float(item["phiStarHigh"]),
                "qT_GeV_leading_small_phi": Z_MASS_GEV * phi_star,
            }
        )
    return rows


def _provider_rows_from_csv(path: Path) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(row for row in handle if not row.lstrip().startswith("#"))
        if reader.fieldnames is None:
            raise ValueError("CSV provider file has no header")
        rows = [dict(row) for row in reader]
    return rows, {"format": "csv", "columns": reader.fieldnames}


def _provider_rows_from_json(path: Path) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    payload = _load_json(path)
    if isinstance(payload.get("rows"), list):
        return payload["rows"], payload
    if isinstance(payload.get("structure_functions"), list):
        return payload["structure_functions"], payload
    raise ValueError("JSON provider must contain a rows or structure_functions list")


def _provider_rows(path: Path) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if path.suffix.lower() == ".csv":
        return _provider_rows_from_csv(path)
    if path.suffix.lower() == ".json":
        return _provider_rows_from_json(path)
    raise ValueError(f"unsupported provider format: {path.suffix}")


def _float_field(row: dict[str, Any], field: str, row_index: int, errors: list[str]) -> float | None:
    if field not in row:
        errors.append(f"row {row_index}: missing {field}")
        return None
    try:
        value = float(row[field])
    except (TypeError, ValueError):
        errors.append(f"row {row_index}: {field} is not numeric: {row[field]!r}")
        return None
    if not math.isfinite(value):
        errors.append(f"row {row_index}: {field} is not finite: {row[field]!r}")
        return None
    return value


def _metadata_value(
    metadata: dict[str, Any],
    cli_value: str | None,
    key: str,
) -> Any:
    if cli_value is not None:
        return cli_value
    return metadata.get(key)


def _validate_provider(
    provider_path: Path,
    rows: list[dict[str, Any]],
    metadata: dict[str, Any],
    strict_grid: list[dict[str, float]],
    args: argparse.Namespace,
) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []

    if len(rows) != len(strict_grid):
        errors.append(f"provider row count {len(rows)} does not match strict grid {len(strict_grid)}")

    source = _metadata_value(metadata, args.source, "source")
    perturbative_order = _metadata_value(metadata, args.perturbative_order, "perturbative_order")
    pdf_set = _metadata_value(metadata, args.pdf_set, "pdf_set")
    fiducial_cuts_hash = _metadata_value(metadata, args.fiducial_cuts_hash, "fiducial_cuts_hash")
    provider_family = _metadata_value(metadata, args.provider_family, "provider_family")

    for key, value in [
        ("source", source),
        ("perturbative_order", perturbative_order),
        ("pdf_set", pdf_set),
        ("fiducial_cuts_hash", fiducial_cuts_hash),
        ("provider_family", provider_family),
    ]:
        if value in (None, ""):
            errors.append(f"missing provider metadata: {key}")

    not_derived = bool(metadata.get("not_derived_from_sigma_inclusive", False))
    if args.assert_independent_provider:
        not_derived = True
    if not not_derived:
        errors.append(
            "provider independence not asserted: set not_derived_from_sigma_inclusive=true "
            "in JSON metadata or pass --assert-independent-provider"
        )

    normalized_rows: list[dict[str, float]] = []
    max_phi_abs_delta = 0.0
    max_qt_abs_delta = 0.0
    for index, row in enumerate(rows):
        normalized: dict[str, float] = {}
        for field in REQUIRED_COLUMNS:
            value = _float_field(row, field, index, errors)
            if value is not None:
                normalized[field] = value
        if index < len(strict_grid) and "phi_star" in normalized:
            expected_phi = strict_grid[index]["phi_star"]
            max_phi_abs_delta = max(max_phi_abs_delta, abs(normalized["phi_star"] - expected_phi))
            if abs(normalized["phi_star"] - expected_phi) > args.phi_tolerance:
                errors.append(
                    f"row {index}: phi_star {normalized['phi_star']} differs from "
                    f"strict grid {expected_phi} by more than {args.phi_tolerance}"
                )
        if "qT_GeV" in normalized and "phi_star" in normalized:
            leading_qt = Z_MASS_GEV * normalized["phi_star"]
            max_qt_abs_delta = max(max_qt_abs_delta, abs(normalized["qT_GeV"] - leading_qt))
            if abs(normalized["qT_GeV"] - leading_qt) > args.qt_tolerance:
                warnings.append(
                    f"row {index}: qT_GeV differs from M_Z*phi_star by "
                    f"{abs(normalized['qT_GeV'] - leading_qt):.6g}; allowed if provider uses exact mapping"
                )
        if all(field in normalized for field in REQUIRED_COLUMNS):
            normalized_rows.append(normalized)

    status = "valid_independent_wi_grid" if not errors else "invalid_or_incomplete_wi_grid"
    return {
        "artifact_schema": "dashi.emst.independent_hadronic_structure_functions.v1",
        "status": status,
        "provider_path": str(provider_path),
        "provider_sha256": _sha256(provider_path),
        "provider_metadata": {
            "source": source,
            "provider_family": provider_family,
            "perturbative_order": perturbative_order,
            "pdf_set": pdf_set,
            "fiducial_cuts_hash": fiducial_cuts_hash,
            "not_derived_from_sigma_inclusive": not_derived,
        },
        "required_columns": REQUIRED_COLUMNS,
        "row_count": len(rows),
        "expected_row_count": len(strict_grid),
        "max_phi_abs_delta": max_phi_abs_delta,
        "max_qT_abs_delta_from_leading_mapping": max_qt_abs_delta,
        "errors": errors,
        "warnings": warnings,
        "rows": normalized_rows if not errors else [],
        "promotion_boundary": (
            "validates provider independence and nine W_i columns only; strict-log "
            "promotion still requires consuming this grid in the fiducial prediction "
            "and passing chi2/dof <= 2 without posterior retuning"
        ),
    }


def _contract_only(strict_artifact: dict[str, Any], strict_path: Path) -> dict[str, Any]:
    selection_metadata = strict_artifact.get("selection_metadata", {})
    return {
        "artifact_schema": "dashi.emst.independent_hadronic_structure_functions.contract.v1",
        "status": "awaiting_independent_wi_provider",
        "strict_artifact": str(strict_path),
        "required_columns": REQUIRED_COLUMNS,
        "component_count": 9,
        "component_names": W_COLUMNS,
        "accepted_provider_families": ["DYTURBO", "ResBos2", "CuTe-MCFM", "EMST-AppendixB"],
        "required_provider_metadata": [
            "source",
            "provider_family",
            "perturbative_order",
            "pdf_set",
            "fiducial_cuts_hash",
            "not_derived_from_sigma_inclusive",
        ],
        "expected_grid": _strict_grid(strict_artifact),
        "selection_metadata_digest": hashlib.sha256(
            json.dumps(selection_metadata, sort_keys=True).encode("utf-8")
        ).hexdigest(),
        "selection_metadata": selection_metadata,
        "promotion_boundary": (
            "contract artifact only; no W_i values supplied, no strict-log promotion possible"
        ),
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Validate or emit the EMST independent nine-component W_i provider contract."
    )
    parser.add_argument("--strict-artifact", default=str(DEFAULT_STRICT_ARTIFACT))
    parser.add_argument("--provider", help="CSV or JSON provider grid with phi_star,qT_GeV,W0..W8.")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--source", help="Provider source/version label.")
    parser.add_argument("--provider-family", help="DYTURBO, ResBos2, CuTe-MCFM, or EMST-AppendixB.")
    parser.add_argument("--perturbative-order", help="Perturbative/resummation order label.")
    parser.add_argument("--pdf-set", help="PDF set used by the provider calculation.")
    parser.add_argument("--fiducial-cuts-hash", help="Hash or version label for the CMS fiducial cuts.")
    parser.add_argument(
        "--assert-independent-provider",
        action="store_true",
        help="Assert this grid was not reconstructed from sigma_dashi_v4 or sigma_inclusive alone.",
    )
    parser.add_argument("--phi-tolerance", type=float, default=1e-12)
    parser.add_argument("--qt-tolerance", type=float, default=1e-6)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    strict_path = Path(args.strict_artifact)
    output_path = Path(args.output)
    strict_artifact = _load_json(strict_path)

    if args.provider is None:
        payload = _contract_only(strict_artifact, strict_path)
        write_json(output_path, payload)
        print(f"EMST W_i provider contract written: {output_path}")
        print("status: awaiting_independent_wi_provider")
        return 0

    provider_path = Path(args.provider)
    try:
        rows, metadata = _provider_rows(provider_path)
        payload = _validate_provider(provider_path, rows, metadata, _strict_grid(strict_artifact), args)
    except ValueError as exc:
        payload = {
            "artifact_schema": "dashi.emst.independent_hadronic_structure_functions.v1",
            "status": "invalid_or_incomplete_wi_grid",
            "provider_path": str(provider_path),
            "provider_sha256": _sha256(provider_path) if provider_path.exists() else None,
            "required_columns": REQUIRED_COLUMNS,
            "errors": [str(exc)],
            "warnings": [],
            "rows": [],
            "promotion_boundary": (
                "invalid provider artifact; no W_i values accepted and no strict-log promotion possible"
            ),
        }
    write_json(output_path, payload)
    print(f"EMST W_i provider validation written: {output_path}")
    print(f"status: {payload['status']}")
    if payload["errors"]:
        for error in payload["errors"]:
            print(f"ERROR: {error}")
        return 2
    for warning in payload["warnings"]:
        print(f"WARNING: {warning}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
