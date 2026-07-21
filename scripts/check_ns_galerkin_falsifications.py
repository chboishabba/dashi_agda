#!/usr/bin/env python3
"""Validate the finite Galerkin trajectory and boundary falsification receipts."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


def digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def load_checked(path: Path) -> tuple[dict[str, Any], bool]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    supplied = payload.pop("sha256", None)
    return payload, supplied == digest(payload)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trajectory-json", type=Path, required=True)
    ap.add_argument("--boundary-json", type=Path, required=True)
    ap.add_argument("--output-json", type=Path, required=True)
    args = ap.parse_args()

    trajectory, trajectory_digest = load_checked(args.trajectory_json)
    boundary, boundary_digest = load_checked(args.boundary_json)
    faces = boundary["faces"]
    checks = {
        "trajectory_digest": trajectory_digest,
        "boundary_digest": boundary_digest,
        "trajectory_energy_decay": trajectory["all_energy_nonincreasing"] is True,
        "trajectory_integrals_finite": trajectory["all_integrals_finite"] is True,
        "trajectory_promotions_false": all(value is False for value in trajectory["promotion"].values()),
        "boundary_promotions_false": all(value is False for value in boundary["promotion"].values()),
        "gamma_sample_inward": faces["gamma_floor"]["strict_inward_on_sample"] is True,
        "off_packet_sample_inward": faces["off_packet_ceiling"]["strict_inward_on_sample"] is True,
        "size_sample_inward": faces["size_ceiling"]["strict_inward_on_sample"] is True,
        "packet_floor_refuted_on_all_samples": faces["packet_energy_floor"]["nonpositive_count"] == 16,
        "all_four_not_promoted": boundary["all_four_strict_on_sample"] is False,
    }
    errors = [name for name, ok in checks.items() if not ok]
    out = {
        "schema": "check_ns_galerkin_falsifications.v1",
        "checks": checks,
        "error_count": len(errors),
        "errors": errors,
        "ok": not errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(out, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
