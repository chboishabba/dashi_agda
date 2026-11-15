#!/usr/bin/env python3
"""Normalize source-specific quantitative evidence for the BH4 system.

This is intentionally fail-closed. It can emit a complete unresolved template
for the major Phase-4 coordinates and, when given a stoichiometric matrix,
automatically adds both reaction-specific `REACTION_FLUX:<RHEA-ID>` and
species-specific `EXCHANGE:<species-id>` coordinates. Missing values remain
`unresolved`; they are never replaced by zero.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

REQUIRED_COORDINATES = [
    "BH4_POOL",
    "BH2_POOL",
    "BH4_BH2_RATIO",
    "GCH1_SYNTHESIS_FLUX",
    "QDPR_RHEA32253_FLUX",
    "PAH_BH4_DEMAND",
    "TH_BH4_DEMAND",
    "TPH1_BH4_DEMAND",
    "TPH2_BH4_DEMAND",
    "NOS1_BH4_DEMAND",
    "NOS2_BH4_DEMAND",
    "NOS3_BH4_DEMAND",
    "AGMO_BH4_DEMAND",
    "BH4_OXIDATION_FLUX",
    "BH4_TRANSPORT_FLUX",
]

VALID_STATUS = {"measured", "derived", "bounded-literature", "unresolved"}


def unresolved_record(parameter_id: str) -> dict:
    return {
        "parameter_id": parameter_id,
        "payment_status": "unresolved",
        "lower": None,
        "upper": None,
        "unit": None,
        "scale_reference": None,
        "source_reference": None,
        "same_object_reference": None,
        "compartment_reference": None,
        "measurement_time_reference": None,
        "method_reference": None,
        "directly_measured": False,
        "usable_for_joint_flux_witness": False,
    }


def reaction_flux_ids(matrix: dict | None) -> list[str]:
    if not matrix:
        return []
    return [f"REACTION_FLUX:{rid}" for rid in matrix.get("reaction_index", [])]


def exchange_ids(matrix: dict | None) -> list[str]:
    if not matrix:
        return []
    return [f"EXCHANGE:{species}" for species in matrix.get("species_index", [])]


def all_coordinate_ids(matrix: dict | None) -> list[str]:
    ids = list(REQUIRED_COORDINATES)
    for pid in reaction_flux_ids(matrix) + exchange_ids(matrix):
        if pid not in ids:
            ids.append(pid)
    return ids


def template(matrix: dict | None = None) -> dict:
    ids = all_coordinate_ids(matrix)
    return {
        "schema": "dashi.bh4-parameter-evidence.v2",
        "parameters": [unresolved_record(pid) for pid in ids],
        "promotion_boundary": {
            "unresolved_means_zero": False,
            "cross_compartment_values_create_same_state": False,
            "cross_time_values_create_same_state": False,
            "literature_bound_is_direct_measurement": False,
            "identity_creates_kinetics": False,
            "kinetic_constant_creates_flux_bound": False,
            "unbounded_exchange_means_zero_exchange": False,
            "parameter_manifest_creates_disease_mechanism": False,
        },
    }


def normalize_row(pid: str, incoming: dict, errors: list[str]) -> dict:
    row = unresolved_record(pid)
    row.update(incoming)
    row["parameter_id"] = pid
    status = str(row.get("payment_status", "unresolved"))
    if status not in VALID_STATUS:
        errors.append(f"{pid}: unsupported payment_status={status}")
        row["payment_status"] = "unresolved"
        status = "unresolved"
    if status != "unresolved":
        if row.get("lower") is None or row.get("upper") is None or not row.get("unit"):
            errors.append(f"{pid}: paid status requires lower/upper/unit")
            return unresolved_record(pid)
        try:
            if float(row["lower"]) > float(row["upper"]):
                errors.append(f"{pid}: lower bound exceeds upper bound")
                return unresolved_record(pid)
        except (TypeError, ValueError):
            errors.append(f"{pid}: bounds must be numeric")
            return unresolved_record(pid)
        if not all(row.get(key) for key in ["source_reference", "same_object_reference", "compartment_reference", "measurement_time_reference"]):
            errors.append(f"{pid}: paid status missing source/same-object/compartment/time coordinate")
            row["usable_for_joint_flux_witness"] = False
    else:
        row["lower"] = None
        row["upper"] = None
        row["usable_for_joint_flux_witness"] = False
    return row


def normalize(payload: dict, matrix: dict | None = None) -> dict:
    records_by_id = {
        str(row.get("parameter_id")): dict(row)
        for row in payload.get("parameters", [])
        if row.get("parameter_id")
    }
    ordered_ids = all_coordinate_ids(matrix)
    for pid in records_by_id:
        if pid not in ordered_ids:
            ordered_ids.append(pid)

    errors: list[str] = []
    normalized = [normalize_row(pid, records_by_id.get(pid, {}), errors) for pid in ordered_ids]
    paid = [row for row in normalized if row["payment_status"] != "unresolved"]
    usable = [row for row in normalized if row.get("usable_for_joint_flux_witness")]
    reaction_rows = [row for row in normalized if str(row["parameter_id"]).startswith("REACTION_FLUX:")]
    exchange_rows = [row for row in normalized if str(row["parameter_id"]).startswith("EXCHANGE:")]
    return {
        "schema": "dashi.bh4-parameter-evidence.v2",
        "parameters": normalized,
        "summary": {
            "required_core": len(REQUIRED_COORDINATES),
            "reaction_flux_coordinates": len(reaction_rows),
            "exchange_coordinates": len(exchange_rows),
            "total_coordinates": len(normalized),
            "paid": len(paid),
            "usable_for_joint_flux_witness": len(usable),
            "unresolved": len(normalized) - len(paid),
            "validation_errors": errors,
        },
        "promotion_boundary": template(matrix)["promotion_boundary"],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--template", action="store_true")
    mode.add_argument("--manifest", type=Path)
    parser.add_argument("--matrix", type=Path, help="optional BH4 stoichiometric matrix; adds reaction-flux and species-exchange coordinates")
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    matrix = json.loads(args.matrix.read_text(encoding="utf-8")) if args.matrix else None
    payload = template(matrix) if args.template else normalize(json.loads(args.manifest.read_text(encoding="utf-8")), matrix)
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    errors = payload.get("summary", {}).get("validation_errors", [])
    return 3 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
