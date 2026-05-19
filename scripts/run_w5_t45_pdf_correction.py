#!/usr/bin/env python3
"""Gated W5 t45 PDF-correction runner.

This runner intentionally does not derive an accepted Drell-Yan luminosity
convention from repo-local CT18 probes.  It only consumes a provider packet
that explicitly accepts or replaces the DY luminosity convention, then computes
R45/R43 = L(M45,Y45) / L(M43,Y43) and emits a pass/fail receipt.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any


EXIT_PROVIDER_PACKET_ABSENT = 44
EXIT_PROVIDER_PACKET_INVALID = 45
EXIT_NEGATIVE_OBSTRUCTION = 46
EXIT_RECEIPT_WRITE_FAILED = 47

TARGET = 0.8804486068
DEFAULT_TOLERANCE = 1.0e-10

REJECTED_LOCAL_PROBES = {
    "fixed_x": 1.0506681065158017,
    "t45_over_z_peak": 0.7514043986785174,
    "t45_over_t43": 0.3348750784006896,
}

REQUIRED_AUTHORITY_FIELDS = (
    "pdf_set",
    "lhapdf_id",
    "grid_checksum",
    "factorization_scale",
    "rapidity_window",
    "mass_bin_integration",
    "flavour_weight_rule",
    "source",
    "provenance",
)


def _finite_float(value: Any, label: str) -> float:
    if isinstance(value, bool):
        raise ValueError(f"{label}: expected finite number, got boolean")
    try:
        number = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{label}: expected finite number, got {value!r}") from exc
    if not math.isfinite(number):
        raise ValueError(f"{label}: expected finite number, got {value!r}")
    return number


def _nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label}: expected nonempty string")
    return value.strip()


def _load_provider_packet(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"provider packet absent: {path}")
    with path.open("r", encoding="utf-8") as handle:
        packet = json.load(handle)
    if not isinstance(packet, dict):
        raise ValueError("provider packet root must be a JSON object")
    return packet


def _validate_provider_packet(packet: dict[str, Any]) -> dict[str, Any]:
    status = _nonempty_string(packet.get("status"), "status")
    if status not in {"accepted", "replacement"}:
        raise ValueError("status must be accepted or replacement")

    authority = packet.get("accepted_dy_luminosity_convention")
    if not isinstance(authority, dict):
        raise ValueError("accepted_dy_luminosity_convention must be an object")

    missing = [field for field in REQUIRED_AUTHORITY_FIELDS if not authority.get(field)]
    if missing:
        raise ValueError(f"accepted convention authority is missing fields: {', '.join(missing)}")

    luminosities = packet.get("luminosities")
    if not isinstance(luminosities, dict):
        raise ValueError("luminosities must be an object")

    l45 = _finite_float(luminosities.get("L_M45_Y45"), "luminosities.L_M45_Y45")
    l43 = _finite_float(luminosities.get("L_M43_Y43"), "luminosities.L_M43_Y43")
    if l43 == 0.0:
        raise ValueError("luminosities.L_M43_Y43 must be nonzero")

    tolerance = _finite_float(packet.get("tolerance", DEFAULT_TOLERANCE), "tolerance")
    if tolerance < 0.0:
        raise ValueError("tolerance must be nonnegative")

    return {
        "status": status,
        "authority": authority,
        "L_M45_Y45": l45,
        "L_M43_Y43": l43,
        "tolerance": tolerance,
    }


def build_receipt(packet_path: Path, validated: dict[str, Any]) -> dict[str, Any]:
    ratio = validated["L_M45_Y45"] / validated["L_M43_Y43"]
    abs_gap = abs(ratio - TARGET)
    passed = abs_gap <= validated["tolerance"]
    result = "success" if passed else "negative_obstruction"
    return {
        "receipt_type": "W5T45Correction",
        "canonical_local_state": "blocked_without_accepted_dy_luminosity_convention",
        "provider_packet": str(packet_path),
        "provider_status": validated["status"],
        "authority_fields": {field: validated["authority"][field] for field in REQUIRED_AUTHORITY_FIELDS},
        "formula": "R45/R43 = L(M45,Y45) / L(M43,Y43)",
        "inputs": {
            "L_M45_Y45": validated["L_M45_Y45"],
            "L_M43_Y43": validated["L_M43_Y43"],
        },
        "computed_R45_over_R43": ratio,
        "target": TARGET,
        "tolerance": validated["tolerance"],
        "abs_gap": abs_gap,
        "result": result,
        "pass": passed,
        "negative_obstruction": None
        if passed
        else "accepted DY convention present, but R45/R43 does not match the W5 t45 target within tolerance",
        "rejected_local_probes": REJECTED_LOCAL_PROBES,
        "governance": {
            "no_w5_promotion": True,
            "no_target_pass_claim_without_accepted_convention_and_tolerance": True,
            "local_ct18_candidate_probes_remain_rejected": True,
        },
    }


def _write_receipt(path: Path, receipt: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(receipt, handle, indent=2, sort_keys=True)
        handle.write("\n")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compute the gated W5 t45 R45/R43 correction from an accepted provider packet."
    )
    parser.add_argument(
        "--provider-packet",
        type=Path,
        required=True,
        help="JSON packet carrying accepted/replacement DY luminosity authority and luminosities.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Optional path for the W5T45Correction JSON receipt.",
    )
    parser.add_argument(
        "--allow-negative-obstruction-exit-zero",
        action="store_true",
        help="Emit a negative obstruction receipt with exit 0 instead of exit 46.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        packet = _load_provider_packet(args.provider_packet)
        validated = _validate_provider_packet(packet)
        receipt = build_receipt(args.provider_packet, validated)
    except FileNotFoundError as exc:
        print(str(exc), file=sys.stderr)
        return EXIT_PROVIDER_PACKET_ABSENT
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"provider packet invalid: {exc}", file=sys.stderr)
        return EXIT_PROVIDER_PACKET_INVALID

    if args.output is not None:
        try:
            _write_receipt(args.output, receipt)
        except OSError as exc:
            print(f"failed to write receipt: {exc}", file=sys.stderr)
            return EXIT_RECEIPT_WRITE_FAILED

    print(json.dumps(receipt, indent=2, sort_keys=True))
    if receipt["pass"] or args.allow_negative_obstruction_exit_zero:
        return 0
    return EXIT_NEGATIVE_OBSTRUCTION


if __name__ == "__main__":
    raise SystemExit(main())
