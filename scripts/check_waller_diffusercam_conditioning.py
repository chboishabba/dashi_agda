#!/usr/bin/env python3
"""Reproducible conditioning audit for the pinned public DiffuserCam PSF stack.

This audit intentionally computes only the depth-code matrix obtained by
vectorising each measured PSF plane at one common lateral source location.
It is a same-artifact diagnostic of depth separation.  It is NOT a global
sparse-scene restricted inverse/RIP certificate for all translated 3-D columns.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import tempfile
import urllib.request
from pathlib import Path

import numpy as np
from scipy.io import loadmat

PINNED_COMMIT = "c8516cb8f482c2bb15e75ebebd91a74b88732c95"
PSF_URL = (
    "https://raw.githubusercontent.com/Waller-Lab/DiffuserCam/"
    + PINNED_COMMIT
    + "/example_data/example_psfs.mat"
)
PSF_GIT_BLOB_SHA1 = "db59065bdaf44fe771a6d3fbe22ae3c703527b5f"
PSF_EXPECTED_BYTES = 10823885


def download_psf(path: Path) -> None:
    urllib.request.urlretrieve(PSF_URL, path)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def analyse(path: Path) -> dict:
    if path.stat().st_size != PSF_EXPECTED_BYTES:
        raise RuntimeError(
            f"unexpected example_psfs.mat byte count: {path.stat().st_size}"
        )

    data = loadmat(path)
    if "psf" not in data:
        raise RuntimeError("pinned MAT artifact does not contain variable 'psf'")

    psf = np.asarray(data["psf"], dtype=np.float64)
    if psf.ndim != 3:
        raise RuntimeError(f"expected 3-D PSF stack, got shape {psf.shape}")

    # Match DiffuserCam_main.m at the pinned commit.
    psf_bias = 102.0
    calibrated = psf - psf_bias

    ny, nx, nz = calibrated.shape
    depth_matrix = calibrated.reshape(ny * nx, nz)
    norms = np.linalg.norm(depth_matrix, axis=0)
    if np.any(norms == 0):
        raise RuntimeError("at least one depth PSF has zero norm after source preprocessing")

    normalized = depth_matrix / norms[None, :]
    gram = normalized.T @ normalized
    offdiag = gram - np.eye(nz)
    max_abs_offdiag = float(np.max(np.abs(offdiag))) if nz > 1 else 0.0
    adjacent_abs = (
        np.abs(np.diag(gram, k=1)) if nz > 1 else np.asarray([], dtype=np.float64)
    )

    singular_values = np.linalg.svd(depth_matrix, compute_uv=False)
    tol = np.finfo(np.float64).eps * max(depth_matrix.shape) * singular_values[0]
    numerical_rank = int(np.count_nonzero(singular_values > tol))
    condition = (
        float(singular_values[0] / singular_values[-1])
        if singular_values[-1] > 0
        else float("inf")
    )

    return {
        "source_repository": "Waller-Lab/DiffuserCam",
        "source_commit": PINNED_COMMIT,
        "artifact": "example_data/example_psfs.mat",
        "artifact_git_blob_sha1": PSF_GIT_BLOB_SHA1,
        "artifact_sha256": sha256_file(path),
        "artifact_bytes": int(path.stat().st_size),
        "psf_shape": [int(ny), int(nx), int(nz)],
        "source_preprocessing": {"psf_bias": psf_bias},
        "diagnostic_scope": "depth_only_same_lateral",
        "depth_columns": int(nz),
        "numerical_rank": numerical_rank,
        "max_abs_normalized_depth_gram_offdiag": max_abs_offdiag,
        "max_abs_adjacent_depth_gram": (
            float(np.max(adjacent_abs)) if adjacent_abs.size else 0.0
        ),
        "mean_abs_adjacent_depth_gram": (
            float(np.mean(adjacent_abs)) if adjacent_abs.size else 0.0
        ),
        "largest_singular_value": float(singular_values[0]),
        "smallest_singular_value": float(singular_values[-1]),
        "depth_matrix_condition_number": condition,
        "global_sparse_inverse_certificate": False,
        "matched_photon_comparison": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--psf", type=Path, default=None)
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()

    if args.psf is None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "example_psfs.mat"
            download_psf(path)
            result = analyse(path)
    else:
        result = analyse(args.psf)

    encoded = json.dumps(result, indent=2, sort_keys=True, allow_nan=False)
    print(encoded)
    if args.json_out is not None:
        args.json_out.write_text(encoded + "\n")


if __name__ == "__main__":
    main()
