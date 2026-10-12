#!/usr/bin/env python3
"""Reproducible conditioning audit for the pinned public DiffuserCam PSF stack.

The audit has two deliberately separated scopes:

1. ``depth_only_same_lateral``: vectorise each measured depth PSF at one common
   lateral origin and inspect depth separation directly.
2. A declared finite translated-column scene family: zero-fill translate each
   depth PSF over a user-selected lateral grid, compute normalized mutual
   coherence, then compile a Gershgorin lower bound for sparse coefficient
   differences.  This is a certificate for exactly that declared finite column
   family, not an all-resolution RIP theorem.

The source preprocessing is pinned to Waller-Lab/DiffuserCam commit
c8516cb8f482c2bb15e75ebebd91a74b88732c95.  The source solver globally
normalises the calibrated PSF stack; this script mirrors that scaling before
constructing translated columns.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
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


def zero_fill_shift2d(image: np.ndarray, dy: int, dx: int) -> np.ndarray:
    """Translate a 2-D PSF and crop back to the sensor rectangle, zero filling."""
    ny, nx = image.shape
    out = np.zeros_like(image)

    src_y0 = max(0, -dy)
    src_y1 = min(ny, ny - dy)
    src_x0 = max(0, -dx)
    src_x1 = min(nx, nx - dx)
    if src_y0 >= src_y1 or src_x0 >= src_x1:
        return out

    dst_y0 = src_y0 + dy
    dst_y1 = src_y1 + dy
    dst_x0 = src_x0 + dx
    dst_x1 = src_x1 + dx
    out[dst_y0:dst_y1, dst_x0:dst_x1] = image[src_y0:src_y1, src_x0:src_x1]
    return out


def translated_column_matrix(
    calibrated_source_scaled: np.ndarray,
    lateral_radius: int,
    lateral_step: int,
) -> tuple[np.ndarray, list[tuple[int, int, int]]]:
    """Build the declared finite cropped shifted-PSF column family."""
    if lateral_radius < 0:
        raise ValueError("lateral_radius must be nonnegative")
    if lateral_step <= 0:
        raise ValueError("lateral_step must be positive")

    ny, nx, nz = calibrated_source_scaled.shape
    shifts = range(-lateral_radius, lateral_radius + 1, lateral_step)
    cols: list[np.ndarray] = []
    labels: list[tuple[int, int, int]] = []
    for z in range(nz):
        plane = calibrated_source_scaled[:, :, z]
        for dy in shifts:
            for dx in shifts:
                col = zero_fill_shift2d(plane, dy, dx).reshape(ny * nx)
                if np.linalg.norm(col) == 0:
                    continue
                cols.append(col)
                labels.append((z, dy, dx))
    if not cols:
        raise RuntimeError("declared translated scene family produced no nonzero columns")
    return np.column_stack(cols), labels


def translated_column_mutual_coherence(columns: np.ndarray) -> tuple[float, float]:
    """Return normalized mutual coherence and minimum unnormalized column norm."""
    norms = np.linalg.norm(columns, axis=0)
    if np.any(norms == 0):
        raise RuntimeError("translated column family contains a zero column")
    normalized = columns / norms[None, :]
    gram = normalized.T @ normalized
    np.fill_diagonal(gram, 0.0)
    mu = float(np.max(np.abs(gram))) if gram.size else 0.0
    return mu, float(np.min(norms))


def gershgorin_sparse_lower_bound(mutual_coherence: float, sparse_order: int) -> float:
    """Lower eigenvalue bound for every normalized Gram submatrix of this order."""
    if sparse_order < 1:
        raise ValueError("sparse_order must be >= 1")
    return max(0.0, 1.0 - (sparse_order - 1) * mutual_coherence)


def max_scene_sparsity_for_positive_bound(mutual_coherence: float, max_columns: int) -> int:
    """Largest k with a positive coherence bound for differences of two k-sparse scenes."""
    best = 0
    for k in range(1, max_columns + 1):
        difference_order = min(2 * k, max_columns)
        if gershgorin_sparse_lower_bound(mutual_coherence, difference_order) > 0.0:
            best = k
        else:
            break
    return best


def analyse(path: Path, lateral_radius: int = 1, lateral_step: int = 1) -> dict:
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

    # Match the global PSF-stack normalization in ADMM3D_solver.m.
    source_stack_norm = float(np.linalg.norm(calibrated.ravel()))
    if source_stack_norm == 0.0:
        raise RuntimeError("calibrated source PSF stack has zero norm")
    source_scaled = calibrated / source_stack_norm

    ny, nx, nz = calibrated.shape
    depth_matrix = source_scaled.reshape(ny * nx, nz)
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

    translated, labels = translated_column_matrix(
        source_scaled,
        lateral_radius=lateral_radius,
        lateral_step=lateral_step,
    )
    mu, min_column_norm = translated_column_mutual_coherence(translated)
    max_scene_k = max_scene_sparsity_for_positive_bound(mu, translated.shape[1])

    sparse_examples = {}
    for scene_k in (1, 2, 4, 8):
        difference_order = min(2 * scene_k, translated.shape[1])
        lower_normalized = gershgorin_sparse_lower_bound(mu, difference_order)
        lower_gain = min_column_norm * math.sqrt(lower_normalized)
        kappa_upper = (1.0 / lower_gain) if lower_gain > 0.0 else None
        sparse_examples[str(scene_k)] = {
            "difference_sparse_order": int(difference_order),
            "normalized_gram_lower_bound": float(lower_normalized),
            "sensor_gain_lower_bound": float(lower_gain),
            "restricted_kappa_upper_bound": kappa_upper,
        }

    global_sparse_inverse_certificate = max_scene_k >= 1

    return {
        "source_repository": "Waller-Lab/DiffuserCam",
        "source_commit": PINNED_COMMIT,
        "artifact": "example_data/example_psfs.mat",
        "artifact_git_blob_sha1": PSF_GIT_BLOB_SHA1,
        "artifact_sha256": sha256_file(path),
        "artifact_bytes": int(path.stat().st_size),
        "psf_shape": [int(ny), int(nx), int(nz)],
        "source_preprocessing": {
            "psf_bias": psf_bias,
            "global_psf_stack_norm": source_stack_norm,
        },
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
        "translated_scene_family": {
            "lateral_radius_pixels": int(lateral_radius),
            "lateral_step_pixels": int(lateral_step),
            "column_count": int(translated.shape[1]),
            "label_count": len(labels),
            "translation_model": "zero_fill_shift_then_sensor_crop",
        },
        "translated_column_mutual_coherence": mu,
        "minimum_translated_column_norm": min_column_norm,
        "max_scene_sparsity_for_positive_bound": int(max_scene_k),
        "gershgorin_sparse_lower_bound": sparse_examples,
        "global_sparse_inverse_certificate": global_sparse_inverse_certificate,
        "certificate_scope": "declared_finite_translated_column_family",
        "all_resolution_camera_rip_certificate": False,
        "matched_photon_comparison": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--psf", type=Path, default=None)
    parser.add_argument("--json-out", type=Path, default=None)
    parser.add_argument("--lateral-radius", type=int, default=1)
    parser.add_argument("--lateral-step", type=int, default=1)
    args = parser.parse_args()

    kwargs = {
        "lateral_radius": args.lateral_radius,
        "lateral_step": args.lateral_step,
    }
    if args.psf is None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "example_psfs.mat"
            download_psf(path)
            result = analyse(path, **kwargs)
    else:
        result = analyse(args.psf, **kwargs)

    encoded = json.dumps(result, indent=2, sort_keys=True, allow_nan=False)
    print(encoded)
    if args.json_out is not None:
        args.json_out.write_text(encoded + "\n")


if __name__ == "__main__":
    main()
