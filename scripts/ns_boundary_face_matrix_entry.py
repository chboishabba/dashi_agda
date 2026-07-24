#!/usr/bin/env python3
"""Run and semantically check one deterministic compact-Gamma boundary face."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from ns_boundary_face_galerkin_search import build

EXPECTED_STRICT = {
    "gamma_floor": True,
    "packet_energy_floor": False,
    "packet_fraction_floor": True,
    "off_packet_ceiling": True,
    "size_ceiling": True,
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--face", choices=sorted(EXPECTED_STRICT), required=True)
    parser.add_argument("--samples", type=int, default=16)
    parser.add_argument("--output-json", type=Path, required=True)
    args = parser.parse_args()

    complete = build(args.samples)
    face = complete["faces"][args.face]
    expected = EXPECTED_STRICT[args.face]
    observed = face["strict_inward_on_sample"] is True
    checks = {
        "parent_schema": complete["schema"] == "ns_boundary_face_galerkin_search.v2",
        "promotion_false": all(value is False for value in complete["promotion"].values()),
        "expected_strict_result": observed is expected,
        "normalized_route_visible": complete["corrected_normalized_route_strict_on_sample"] is True,
        "absolute_route_rejected": complete["original_absolute_floor_route_strict_on_sample"] is False,
        "absolute_floor_failure_visible": (
            args.face != "packet_energy_floor"
            or face["nonpositive_count"] == args.samples
        ),
    }
    errors = [name for name, ok in checks.items() if not ok]
    payload = {
        "schema": "ns_boundary_face_matrix_entry.v1",
        "face": args.face,
        "sample_count": args.samples,
        "expected_strict_on_sample": expected,
        "observed": face,
        "checks": checks,
        "error_count": len(errors),
        "errors": errors,
        "ok": not errors,
        "promotion": {
            "finite_face_job_is_proof": False,
            "strict_Dini_inwardness": False,
        },
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(payload, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
