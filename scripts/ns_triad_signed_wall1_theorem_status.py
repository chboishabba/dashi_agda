#!/usr/bin/env python3
"""Consolidate the signed-XOR and signed-spectral Wall 1 receipts into one fail-closed status surface."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_signed_wall1_theorem_status.py"
CONTRACT = "ns_triad_signed_wall1_theorem_status"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_WALL1_THEOREM_STATUS"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_SIGNED_XOR_AGDA = Path("DASHI/Physics/Closure/NSTriadSignedXORGaugeabilityBoundary.agda")
DEFAULT_SIGNED_SPECTRAL_AGDA = Path("DASHI/Physics/Closure/NSTriadSignedSpectralFrustrationBoundary.agda")
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_wall1_theorem_status_20260621.json"
)

CONTROL_CARD = {
    "O": "Consolidate the signed-XOR and signed-spectral Wall 1 receipts into one fail-closed status surface.",
    "R": (
        "Read the signed-XOR gaugeability boundary and signed spectral-frustration boundary, "
        "then expose a compact status receipt for the Wall 1 integration path."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only status surface; the signed-XOR and signed-spectral routes remain empirical and non-promoting.",
    "L": (
        "Load the two signed Wall 1 receipts, preserve their canonical summaries, and emit a single "
        "consolidated fail-closed status JSON."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from these signed Wall 1 receipts.",
    "F": "The signed-XOR and signed-spectral surfaces remain open; this script records that they are not promoted.",
}

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--signed-xor-agda", type=Path, default=DEFAULT_SIGNED_XOR_AGDA)
    parser.add_argument("--signed-spectral-agda", type=Path, default=DEFAULT_SIGNED_SPECTRAL_AGDA)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"missing source agda file: {path}")
    return path.read_text(encoding="utf-8")


def _extract_string(text: str, name: str) -> str:
    pattern = re.compile(rf"^{re.escape(name)}\s*=\s*$\n\s*\"([^\"]*)\"", re.MULTILINE)
    match = pattern.search(text)
    if not match:
        raise ValueError(f"missing string assignment for {name}")
    return match.group(1)


def _has_marker(text: str, marker: str) -> bool:
    return marker in text


def _build_signed_xor_row(text: str, path: Path) -> dict[str, Any]:
    if not _has_marker(text, "canonicalWeightedDistanceTargetText"):
        raise ValueError(f"{path}: missing canonicalWeightedDistanceTargetText")
    return {
        "surface": "signed_xor_gaugeability",
        "module_path": str(path),
        "receipt_name": "NSTriadSignedXORGaugeabilityBoundary",
        "route_name": "wall1a-signed-xor-gaugeability",
        "boundary_summary": _extract_string(text, "canonicalSText"),
        "bridge_summary": _extract_string(text, "canonicalFText"),
        "target_text": _extract_string(text, "canonicalWeightedDistanceTargetText"),
        "candidate_only": True,
        "fail_closed": True,
        "bridge_open": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "wall1_status": "unproved",
    }


def _build_signed_spectral_row(text: str, path: Path) -> dict[str, Any]:
    return {
        "surface": "signed_spectral_frustration",
        "module_path": str(path),
        "receipt_name": _extract_string(text, "boundaryName"),
        "route_name": _extract_string(text, "routeName"),
        "boundary_summary": _extract_string(text, "boundarySummary"),
        "bridge_summary": _extract_string(text, "bridgeSummary"),
        "candidate_only": True,
        "fail_closed": True,
        "primary_wall1a_candidate": True,
        "upper_spectral_edge_risk": True,
        "signed_xor_bridge_open": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "wall1_status": "unproved",
    }


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    signed_xor_text = ""
    signed_spectral_text = ""
    try:
        signed_xor_text = _read_text(Path(args.signed_xor_agda))
    except Exception as exc:  # noqa: BLE001
        errors.append(str(exc))
    try:
        signed_spectral_text = _read_text(Path(args.signed_spectral_agda))
    except Exception as exc:  # noqa: BLE001
        errors.append(str(exc))

    rows: list[dict[str, Any]] = []
    if not errors:
        try:
            rows.append(_build_signed_xor_row(signed_xor_text, Path(args.signed_xor_agda)))
            rows.append(_build_signed_spectral_row(signed_spectral_text, Path(args.signed_spectral_agda)))
        except Exception as exc:  # noqa: BLE001
            errors.append(str(exc))

    aggregate = {
        "surface_count": int(len(rows)),
        "signed_xor_bridge_open": bool(rows[0]["bridge_open"]) if len(rows) >= 1 else False,
        "signed_spectral_bridge_open": bool(rows[1]["signed_xor_bridge_open"]) if len(rows) >= 2 else False,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "wall1_status": "unproved" if rows else "unproved",
        "signed_surface_consensus": "fail-closed" if rows and not errors else "unavailable",
    }

    status = OK_STATUS if not errors else ERROR_STATUS
    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "status": status,
        "ok": status == OK_STATUS,
        "inputs": {
            "signed_xor_agda": str(args.signed_xor_agda),
            "signed_spectral_agda": str(args.signed_spectral_agda),
            "output_json": str(args.output_json),
        },
        "rows": rows,
        "aggregate": aggregate,
        "warnings": [],
        "errors": errors,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
