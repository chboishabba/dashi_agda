#!/usr/bin/env python3
"""Validate the deterministic common normalized boundary tuple diagnostic."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

SCHEMA = "ns_common_normalized_parameter_tuple_certificate.v1"
FACES = (
    "gamma_floor",
    "packet_fraction_floor",
    "off_packet_ceiling",
    "size_ceiling",
)


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    args = parser.parse_args()

    payload = json.loads(args.source_json.read_text(encoding="utf-8"))
    supplied = payload.pop("sha256", None)
    faces = payload.get("faces", {})
    promotion = payload.get("promotion", {})
    selected = payload.get("selected_tuple", {})

    checks = {
        "schema": payload.get("schema") == SCHEMA,
        "authority": payload.get("authority")
        == "finite_deterministic_common_tuple_diagnostic_only",
        "digest": supplied == digest(payload),
        "all_faces_present": all(face in faces for face in FACES),
        "selected_tuple_exact": selected
        == {
            "gamma_floor": "7.0000000000e-02",
            "packet_fraction_floor": "6.4000000000e-01",
            "off_packet_ceiling": "3.6000000000e-01",
            "size_squared_ceiling": "4.5000000000e+01",
        },
        "partition_identity": payload.get("packet_fraction_plus_off_packet")
        == "1.0000000000e+00",
        "all_faces_strict": payload.get("all_faces_strict_inward_on_sample") is True,
        "all_witnesses_share_common_region": payload.get(
            "all_face_witnesses_use_common_region"
        )
        is True,
        "face_counts_positive": all(
            int(faces.get(face, {}).get("sample_count", 0)) > 0 for face in FACES
        ),
        "face_nonpositive_counts_zero": all(
            int(faces.get(face, {}).get("nonpositive_count", -1)) == 0
            for face in FACES
        ),
        "face_minima_positive": all(
            float(faces.get(face, {}).get("minimum_inward_derivative", "nan")) > 0.0
            for face in FACES
        ),
        "no_promotion": bool(promotion)
        and all(value is False for value in promotion.values()),
    }
    errors = [name for name, ok in checks.items() if not ok]
    output = {
        "schema": "check_ns_common_normalized_parameter_tuple_certificate.v1",
        "checks": checks,
        "errors": errors,
        "error_count": len(errors),
        "ok": not errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(output, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(output, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
