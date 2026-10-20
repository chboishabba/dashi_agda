#!/usr/bin/env python3
"""Plan a memory-safe finite DiffuserCam source-H claim scale.

The real conditioning audit forms a dense selected-column matrix and then a
dense normalized Gram matrix.  This planner estimates that working set before
those allocations occur.  It is an execution/resource planner only: a safe
candidate is not a conditioning theorem, a real-data receipt, or a physical
calibration.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from scipy.io import whosmat

FLOAT64_BYTES = 8
GIB = 1024**3


def _offset_count(lateral_radius: int, lateral_step: int) -> int:
    if lateral_radius < 0:
        raise ValueError("lateral_radius must be nonnegative")
    if lateral_step <= 0:
        raise ValueError("lateral_step must be positive")
    return len(range(-lateral_radius, lateral_radius + 1, lateral_step))


def estimate_dense_working_set(
    ny: int,
    nx: int,
    nz: int,
    *,
    lateral_radius: int,
    lateral_step: int,
    dtype_bytes: int = FLOAT64_BYTES,
) -> dict:
    if min(ny, nx, nz, dtype_bytes) <= 0:
        raise ValueError("array dimensions and dtype_bytes must be positive")

    one_axis = _offset_count(lateral_radius, lateral_step)
    lateral_positions = one_axis * one_axis
    sensor_pixels = ny * nx
    selected_columns = nz * lateral_positions

    selected_h_bytes = sensor_pixels * selected_columns * dtype_bytes
    gram_bytes = selected_columns * selected_columns * dtype_bytes

    # H remains resident while a normalized copy and Gram are formed.
    resident_lower_bound_bytes = 2 * selected_h_bytes + gram_bytes
    # Conservative allowance for a transient extra H-sized copy during column
    # stacking / normalization. This is a planning guard, not a profiler trace.
    conservative_peak_bytes = 3 * selected_h_bytes + gram_bytes

    return {
        "ny": int(ny),
        "nx": int(nx),
        "nz": int(nz),
        "dtype_bytes": int(dtype_bytes),
        "lateral_radius": int(lateral_radius),
        "lateral_step": int(lateral_step),
        "lateral_positions": int(lateral_positions),
        "sensor_pixels": int(sensor_pixels),
        "selected_columns": int(selected_columns),
        "selected_h_bytes": int(selected_h_bytes),
        "gram_bytes": int(gram_bytes),
        "resident_lower_bound_bytes": int(resident_lower_bound_bytes),
        "conservative_peak_bytes": int(conservative_peak_bytes),
    }


def plan_claim_scales(
    ny: int,
    nx: int,
    nz: int,
    *,
    budget_bytes: int,
    radii=(0, 1, 2),
    steps=(1,),
) -> dict:
    if budget_bytes <= 0:
        raise ValueError("budget_bytes must be positive")

    candidates = []
    for radius in radii:
        for step in steps:
            item = estimate_dense_working_set(
                ny,
                nx,
                nz,
                lateral_radius=int(radius),
                lateral_step=int(step),
            )
            item["safe"] = item["conservative_peak_bytes"] <= budget_bytes
            item["budget_fraction"] = item["conservative_peak_bytes"] / budget_bytes
            candidates.append(item)

    safe = [item for item in candidates if item["safe"]]
    largest_safe = max(safe, key=lambda item: item["selected_columns"], default=None)

    return {
        "shape": [int(ny), int(nx), int(nz)],
        "budget_bytes": int(budget_bytes),
        "budget_gib": float(budget_bytes / GIB),
        "candidates": candidates,
        "largest_safe_candidate": largest_safe,
        "planner_is_numerical_certificate": False,
        "planner_is_physical_receipt": False,
    }


def psf_shape_from_mat(path: Path, variable: str = "psf") -> tuple[int, int, int]:
    for name, shape, _dtype in whosmat(path):
        if name == variable:
            if len(shape) != 3:
                raise RuntimeError(f"{variable!r} is not 3-D: shape={shape}")
            return int(shape[0]), int(shape[1]), int(shape[2])
    raise RuntimeError(f"MAT artifact does not contain variable {variable!r}")


def _parse_int_csv(value: str) -> tuple[int, ...]:
    parsed = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if not parsed:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return parsed


def main() -> None:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--psf", type=Path)
    source.add_argument("--shape", nargs=3, type=int, metavar=("NY", "NX", "NZ"))
    parser.add_argument("--budget-gib", type=float, default=5.0)
    parser.add_argument("--radii", type=_parse_int_csv, default=(0, 1, 2))
    parser.add_argument("--steps", type=_parse_int_csv, default=(1,))
    parser.add_argument("--require-safe-radius", type=int, default=None)
    parser.add_argument("--require-safe-step", type=int, default=1)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()

    if args.psf is not None:
        ny, nx, nz = psf_shape_from_mat(args.psf)
    else:
        ny, nx, nz = (int(v) for v in args.shape)

    budget_bytes = int(args.budget_gib * GIB)
    plan = plan_claim_scales(
        ny,
        nx,
        nz,
        budget_bytes=budget_bytes,
        radii=args.radii,
        steps=args.steps,
    )

    encoded = json.dumps(plan, indent=2, sort_keys=True, allow_nan=False)
    print(encoded)
    if args.json_out is not None:
        args.json_out.write_text(encoded + "\n")

    if args.require_safe_radius is not None:
        requested = [
            item
            for item in plan["candidates"]
            if item["lateral_radius"] == args.require_safe_radius
            and item["lateral_step"] == args.require_safe_step
        ]
        if not requested:
            raise SystemExit("required radius/step pair was not included in candidate plan")
        if not requested[0]["safe"]:
            raise SystemExit(
                "required selected-H claim scale exceeds conservative memory budget: "
                f"radius={args.require_safe_radius}, step={args.require_safe_step}, "
                f"peak={requested[0]['conservative_peak_bytes']} bytes, "
                f"budget={budget_bytes} bytes"
            )


if __name__ == "__main__":
    main()
