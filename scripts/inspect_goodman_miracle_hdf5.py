#!/usr/bin/env python3
"""Read-only MIRACLE v4 HDF5 schema/position inspector.

Original measurement ownership: Kujawski, Pelling and Sarradj (2024),
DOI 10.1186/s13636-024-00352-8; version-4 dataset DOI
10.14279/depositonce-20837. No audio model is trained or evaluated.
Requires h5py; never loads the multi-GB impulse_response dataset into RAM.
"""
import argparse
import json
import math
from pathlib import Path

SIZES = {"A1": 4096, "A2": 4096, "D1": 1089, "R2": 4096}


def inspect_file(path, scenario, block_size_m):
    try:
        import h5py
    except ImportError as exc:
        raise RuntimeError("h5py required; install in isolated analysis environment") from exc
    if scenario not in SIZES:
        raise ValueError("unsupported scenario")
    if not math.isfinite(block_size_m) or block_size_m <= 0:
        raise ValueError("block size must be a positive finite number of metres")
    with h5py.File(path, "r") as h:
        needed = (
            "data/impulse_response", "location/source",
            "location/receiver", "metadata/sampling_rate",
            "metadata/c0", "metadata/temperature",
        )
        if any(key not in h for key in needed):
            raise ValueError("required MIRACLE HDF5 key missing")
        impulse = h["data/impulse_response"]
        positions = h["location/source"]
        receivers = h["location/receiver"]
        if len(impulse.shape) != 3:
            raise ValueError("impulse_response must be 3-dimensional")
        count = SIZES[scenario]
        if impulse.shape[0] != count or impulse.shape[1] != 64 or impulse.shape[2] <= 0:
            raise ValueError("unexpected impulse response dimensions")
        if positions.shape != (count, 3) or receivers.shape != (64, 3):
            raise ValueError("source/receiver coordinate dimensions mismatch")
        sr = h["metadata/sampling_rate"][()]
        fs = float(sr)
        if not math.isfinite(fs) or fs <= 0:
            raise ValueError("invalid sampling rate")
        coords = positions[()]
        mic = receivers[()]
        if not all(math.isfinite(float(v)) for xyz in coords for v in xyz):
            raise ValueError("nonfinite source coordinates")
        if not all(math.isfinite(float(v)) for xyz in mic for v in xyz):
            raise ValueError("nonfinite receiver coordinates")
        # Block IDs depend only on trusted metric location coordinates.
        rows = []
        for i, xyz in enumerate(coords):
            xyz_m = [float(v) for v in xyz]
            cell = [math.floor(v / block_size_m) for v in xyz_m]
            rows.append({"scenario": scenario, "position_id": str(i),
                         "xyz_m": xyz_m, "spatial_block": ":".join(map(str, cell))})
        c0 = h["metadata/c0"]
        temperature = h["metadata/temperature"]
        if c0.shape not in ((count,), ()) or temperature.shape not in ((count,), ()):
            raise ValueError("speed of sound / temperature sample count mismatch")
        return rows, {
            "scenario": scenario, "sources": count, "receivers": 64,
            "impulse_samples": impulse.shape[2], "sampling_rate_hz": fs,
            "position_units": "metres (requires confirmation from dataset documentation)",
            "calibrated_pressure_units_verified": False,
            "replicate_noise_covariance_measured": False,
        }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--archive-root", type=Path, required=True)
    ap.add_argument("--block-size-m", type=float, required=True)
    ap.add_argument("--positions-out", type=Path, required=True)
    ap.add_argument("--schema-out", type=Path, required=True)
    args = ap.parse_args()
    all_rows, info = [], []
    for name in ("A1", "A2", "D1", "R2"):
        rows, metadata = inspect_file(args.archive_root / (name + ".h5"),
                                      name, args.block_size_m)
        all_rows.extend(rows)
        info.append(metadata)
    if len(all_rows) != 13377:
        raise ValueError("expected 13,377 original source positions")
    args.positions_out.write_text(json.dumps(all_rows, indent=2) + "\n")
    args.schema_out.write_text(json.dumps({
        "dataset_doi": "10.14279/depositonce-20837",
        "observed_hdf5_schema": info,
        "heldout_accuracy": None,
        "calibration_statement": "No absolute SPL or noise covariance inferred"
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
