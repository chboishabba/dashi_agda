#!/usr/bin/env python3
"""Build DY luminosity artifacts from an accepted authority-shaped packet.

This adapter is readiness infrastructure for W4/W5.  It intentionally does not
derive or accept a Drell-Yan luminosity convention locally.  It only consumes a
provider packet that already carries accepted/replacement authority fields and
provider-supplied luminosities.
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


EXIT_PACKET_ABSENT = 50
EXIT_PACKET_INVALID = 51
EXIT_WRITE_FAILED = 52

ACCEPTED_STATUSES = {"accepted", "replacement"}

REQUIRED_RESPONSE_FIELDS = (
    "provider_name",
    "provider_role",
    "pdf_set_version",
    "lhapdf_id",
    "member_id",
    "grid_checksum",
    "scale_convention",
    "rapidity_window",
    "mass_bin_rule",
    "flavour_weight_rule",
    "integration_method",
    "source_citation",
    "attestation_no_manual_overfit",
)

W4_AUTHORITY_FIELD_MAP = {
    "pdfSet": "pdf_set_version",
    "lhapdfId": "lhapdf_id",
    "gridChecksum": "grid_checksum",
    "scaleConvention": "scale_convention",
    "rapidityConvention": "rapidity_window",
    "massBinRule": "mass_bin_rule",
    "flavourWeights": "flavour_weight_rule",
    "interpolationIntegration": "integration_method",
    "source": "source_citation",
    "provenance": "provenance_hash",
}

W5_AUTHORITY_FIELD_MAP = {
    "pdf_set": "pdf_set_version",
    "lhapdf_id": "lhapdf_id",
    "grid_checksum": "grid_checksum",
    "factorization_scale": "scale_convention",
    "rapidity_window": "rapidity_window",
    "mass_bin_integration": "mass_bin_rule",
    "flavour_weight_rule": "flavour_weight_rule",
    "source": "source_citation",
    "provenance": "provenance_hash",
}

L43_KEYS = (
    "L43",
    "L_M43_Y43",
    "L_50_76",
    "L_M50_76",
    "luminosity_43",
)

L45_KEYS = (
    "L45",
    "L_M45_Y45",
    "L_106_170",
    "L_M106_170",
    "luminosity_45",
)

W4_KEYS = (
    "W4_per_bin",
    "W4_per_bin_luminosities",
    "W4_luminosity_bins",
    "W4_luminosities",
    "L_W4_bins",
    "z_peak_per_bin_luminosities",
)


def stable_digest(payload: Any) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"authority packet absent: {path}")
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError("authority packet root must be a JSON object")
    return payload


def nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label}: expected nonempty string")
    return value.strip()


def finite_float(value: Any, label: str) -> float:
    if isinstance(value, bool):
        raise ValueError(f"{label}: expected finite number, got boolean")
    try:
        number = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{label}: expected finite number, got {value!r}") from exc
    if not math.isfinite(number):
        raise ValueError(f"{label}: expected finite number, got {value!r}")
    return number


def require_positive(value: float, label: str) -> float:
    if value <= 0.0:
        raise ValueError(f"{label}: expected positive number")
    return value


def first_present(mapping: dict[str, Any], keys: tuple[str, ...], label: str) -> Any:
    for key in keys:
        if key in mapping:
            return mapping[key]
    raise ValueError(f"{label}: missing any of {', '.join(keys)}")


def choose_authority_payload(packet: dict[str, Any]) -> dict[str, Any]:
    for key in (
        "authority_response",
        "accepted_dy_luminosity_convention_authority",
        "accepted_dy_luminosity_convention",
        "authority",
    ):
        value = packet.get(key)
        if isinstance(value, dict):
            merged = dict(value)
            if "status" not in merged and "status" in packet:
                merged["status"] = packet["status"]
            return merged
    return packet


def normalize_authority(packet: dict[str, Any]) -> dict[str, str]:
    authority = choose_authority_payload(packet)
    status = nonempty_string(authority.get("status", packet.get("status")), "status")
    if status not in ACCEPTED_STATUSES:
        raise ValueError("authority status must be accepted or replacement")

    normalized = {"status": status}
    missing = []
    for field in REQUIRED_RESPONSE_FIELDS:
        value = authority.get(field, packet.get(field))
        if value is None:
            missing.append(field)
            continue
        normalized[field] = nonempty_string(value, field)
    if missing:
        raise ValueError(f"accepted authority is missing fields: {', '.join(missing)}")

    return normalized


def choose_luminosity_payload(packet: dict[str, Any]) -> dict[str, Any]:
    luminosities = packet.get("luminosities")
    if isinstance(luminosities, dict):
        merged = dict(luminosities)
        for key in W4_KEYS:
            if key in packet and key not in merged:
                merged[key] = packet[key]
        return merged
    return packet


def normalize_w4_bins(raw: Any) -> list[float]:
    if not isinstance(raw, list):
        raise ValueError("W4 per-bin luminosities must be a list")

    values: list[float] = []
    for index, item in enumerate(raw):
        if isinstance(item, dict):
            for key in ("luminosity", "L", "value"):
                if key in item:
                    values.append(require_positive(finite_float(item[key], f"W4[{index}].{key}"), f"W4[{index}]"))
                    break
            else:
                raise ValueError(f"W4[{index}]: object must contain luminosity, L, or value")
        else:
            values.append(require_positive(finite_float(item, f"W4[{index}]"), f"W4[{index}]"))

    if not values:
        raise ValueError("W4 per-bin luminosities must not be empty")
    return values


def normalize_luminosities(packet: dict[str, Any]) -> dict[str, Any]:
    luminosities = choose_luminosity_payload(packet)
    l43 = require_positive(
        finite_float(first_present(luminosities, L43_KEYS, "L43 luminosity"), "L43"),
        "L43",
    )
    l45 = require_positive(
        finite_float(first_present(luminosities, L45_KEYS, "L45 luminosity"), "L45"),
        "L45",
    )
    w4_raw = first_present(luminosities, W4_KEYS, "W4 per-bin luminosities")
    return {
        "L43": l43,
        "L45": l45,
        "R45_over_43": l45 / l43,
        "W4_per_bin_luminosities": normalize_w4_bins(w4_raw),
    }


def build_w4_authority(authority: dict[str, str], provenance_hash: str) -> dict[str, str]:
    enriched = {**authority, "provenance_hash": provenance_hash}
    return {
        "status": authority["status"],
        **{target: enriched[source] for target, source in W4_AUTHORITY_FIELD_MAP.items()},
    }


def build_w5_provider_packet(authority: dict[str, str], luminosities: dict[str, Any], provenance_hash: str) -> dict[str, Any]:
    enriched = {**authority, "provenance_hash": provenance_hash}
    return {
        "status": authority["status"],
        "accepted_dy_luminosity_convention": {
            target: enriched[source] for target, source in W5_AUTHORITY_FIELD_MAP.items()
        },
        "luminosities": {
            "L_M45_Y45": luminosities["L45"],
            "L_M43_Y43": luminosities["L43"],
        },
    }


def build_artifact(packet_path: Path, packet: dict[str, Any]) -> dict[str, Any]:
    authority = normalize_authority(packet)
    luminosities = normalize_luminosities(packet)
    provenance_source = {
        "packet_sha256": sha256_file(packet_path),
        "authority": authority,
        "luminosities": luminosities,
    }
    provenance_hash = stable_digest(provenance_source)
    return {
        "artifactSchema": "dashi-dy-luminosity-from-authority-packet-v1",
        "schemaVersion": "0.1.0",
        "status": "computed-not-promoted",
        "sourcePacket": str(packet_path),
        "sourcePacketSha256": provenance_source["packet_sha256"],
        "authorityStatus": authority["status"],
        "authorityFields": authority,
        "luminosities": luminosities,
        "outputs": {
            "L43": luminosities["L43"],
            "L45": luminosities["L45"],
            "R45_over_43": luminosities["R45_over_43"],
            "W4_per_bin_luminosities": luminosities["W4_per_bin_luminosities"],
            "provenance_hash": provenance_hash,
        },
        "downstreamArtifacts": {
            "w4AcceptedDYLuminosityAuthority": build_w4_authority(authority, provenance_hash),
            "w5ProviderPacket": build_w5_provider_packet(authority, luminosities, provenance_hash),
        },
        "governance": {
            "no_w4_promotion": True,
            "no_w5_promotion": True,
            "no_authority_fabricated": True,
            "requires_external_provider_packet_with_accepted_or_replacement_status": True,
        },
        "provenanceHash": provenance_hash,
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_w4_luminosity_csv(path: Path, luminosities: list[float]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=("index", "luminosity"))
        writer.writeheader()
        for index, value in enumerate(luminosities):
            writer.writerow({"index": index, "luminosity": repr(value)})


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Fail-closed adapter from accepted DY authority JSON to W4/W5 luminosity artifacts. "
            "The input must already carry accepted/replacement authority and provider luminosities."
        )
    )
    parser.add_argument(
        "--authority-packet",
        type=Path,
        required=True,
        help="Accepted/replacement provider JSON carrying convention fields and luminosities.",
    )
    parser.add_argument("--output", type=Path, help="Write the full adapter artifact JSON.")
    parser.add_argument(
        "--write-w4-luminosity-csv",
        type=Path,
        help="Optional CSV path with columns index,luminosity for run_w4_z_peak_adequacy.py.",
    )
    parser.add_argument(
        "--write-w4-authority-json",
        type=Path,
        help="Optional authority JSON path compatible with run_w4_z_peak_adequacy.py.",
    )
    parser.add_argument(
        "--write-w5-provider-packet",
        type=Path,
        help="Optional provider packet JSON path compatible with run_w5_t45_pdf_correction.py.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        packet = load_json(args.authority_packet)
        artifact = build_artifact(args.authority_packet, packet)
        if args.output is not None:
            write_json(args.output, artifact)
        if args.write_w4_luminosity_csv is not None:
            write_w4_luminosity_csv(
                args.write_w4_luminosity_csv,
                artifact["outputs"]["W4_per_bin_luminosities"],
            )
        if args.write_w4_authority_json is not None:
            write_json(
                args.write_w4_authority_json,
                artifact["downstreamArtifacts"]["w4AcceptedDYLuminosityAuthority"],
            )
        if args.write_w5_provider_packet is not None:
            write_json(
                args.write_w5_provider_packet,
                artifact["downstreamArtifacts"]["w5ProviderPacket"],
            )
    except FileNotFoundError as exc:
        print(str(exc), file=sys.stderr)
        return EXIT_PACKET_ABSENT
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"authority packet invalid: {exc}", file=sys.stderr)
        return EXIT_PACKET_INVALID

    print(json.dumps(artifact, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
