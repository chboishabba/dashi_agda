"""Degeneracy-safe subspace topology for a literal Co1/4TaSe2 Wannier model.

This consumer is conditional on an independently acquired same-object material
Hamiltonian.  It computes gauge-invariant topology for an *isolated band
subspace*, allowing degeneracies inside that selected subspace.  It does not
turn the current toy/source-compatible Hamiltonians into material evidence.

The central object is the spectral projector P onto selected bands.  For an
isolated subspace, derivatives are obtained from dH without choosing a gauge
inside degenerate selected/complementary blocks, and the trace curvature is

    F_ab = -i Tr P [d_a P, d_b P].

Wilson loops use the unitary polar part of consecutive subspace overlaps, so
only the closed-loop spectrum is reported.  Metallic anomalous-Hall/spin-Hall
conductivity is deliberately NOT produced here: a Fermi-surface occupation and
scattering/response prescription is a separate physical input.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

try:
    import co_tase2_wannier90_spectral as w90
    import co_tase2_wannier3d_diagnostics as diag3d
except ImportError:
    w90 = None
    diag3d = None


def _validate_subspace(evals, selected, gap_floor=1e-8):
    e = np.asarray(evals, float)
    sel = np.asarray(sorted(set(int(i) for i in selected)), int)
    if sel.size == 0 or sel.size >= e.size:
        raise ValueError("selected subspace must be non-empty and not the full Hilbert space")
    if np.any(sel < 0) or np.any(sel >= e.size):
        raise ValueError("selected band index out of range")
    mask = np.ones(e.size, bool)
    mask[sel] = False
    comp = np.where(mask)[0]
    gap = float(np.min(np.abs(e[sel, None] - e[comp][None, :])))
    if not np.isfinite(gap) or gap <= float(gap_floor):
        raise ValueError(f"selected subspace is not isolated: external gap={gap:g}")
    return sel, comp, gap


def projector_and_derivatives(evals, evecs, derivs, selected, gap_floor=1e-8):
    """Return P, [dP/dk_a], and the selected/complement external gap.

    Degeneracies within the selected block or within its complement are allowed.
    Only the gap between the two subspaces must remain open.
    """
    e = np.asarray(evals, float)
    u = np.asarray(evecs, complex)
    n = e.size
    if u.shape != (n, n):
        raise ValueError("eigenvector matrix shape mismatch")
    ds = [np.asarray(d, complex) for d in derivs]
    if len(ds) != 3 or any(d.shape != (n, n) for d in ds):
        raise ValueError("exactly three Hamiltonian derivatives are required")

    sel, comp, gap = _validate_subspace(e, selected, gap_floor)
    us = u[:, sel]
    projector = us @ us.conj().T
    dprojectors = []
    for dH in ds:
        dP = np.zeros((n, n), complex)
        for i in sel:
            for a in comp:
                amp = np.vdot(u[:, a], dH @ u[:, i]) / (e[i] - e[a])
                dP += (
                    amp * np.outer(u[:, a], u[:, i].conj())
                    + np.conj(amp) * np.outer(u[:, i], u[:, a].conj())
                )
        dprojectors.append(dP)
    return projector, dprojectors, gap


def subspace_curvature_vector(evals, evecs, derivs, selected, gap_floor=1e-8):
    """Trace Berry curvature (F_yz,F_zx,F_xy) of an isolated band subspace."""
    p, dp, _ = projector_and_derivatives(
        evals, evecs, derivs, selected, gap_floor=gap_floor
    )
    out = np.empty(3, float)
    for idx, (a, b) in enumerate(((1, 2), (2, 0), (0, 1))):
        comm = dp[a] @ dp[b] - dp[b] @ dp[a]
        out[idx] = float(np.real(-1j * np.trace(p @ comm)))
    return out


def subspace_frame(evals, evecs, selected, gap_floor=1e-8):
    sel, _, gap = _validate_subspace(evals, selected, gap_floor)
    frame = np.asarray(evecs, complex)[:, sel]
    return frame, gap


def wilson_loop_phases(frames, singular_floor=1e-10):
    """Gauge-invariant eigenphases of a closed discrete Wilson loop.

    Each frame has shape (Hilbert dimension, subspace rank).  The unitary polar
    factor of each overlap is used to avoid arbitrary normalization drift.
    """
    fs = [np.asarray(f, complex) for f in frames]
    if len(fs) < 3:
        raise ValueError("Wilson loop requires at least three frames")
    n, rank = fs[0].shape
    if rank < 1 or any(f.shape != (n, rank) for f in fs):
        raise ValueError("Wilson-loop frame shape mismatch")
    ident = np.eye(rank)
    for f in fs:
        if np.max(np.abs(f.conj().T @ f - ident)) > 1e-8:
            raise ValueError("Wilson-loop frames must be orthonormal")

    loop = np.eye(rank, dtype=complex)
    min_overlap_sv = np.inf
    for i in range(len(fs)):
        overlap = fs[i].conj().T @ fs[(i + 1) % len(fs)]
        left, singular, right_h = np.linalg.svd(overlap)
        min_overlap_sv = min(min_overlap_sv, float(np.min(singular)))
        if np.min(singular) <= singular_floor:
            raise ValueError("Wilson-loop neighboring subspaces have singular overlap")
        link = left @ right_h
        loop = loop @ link
    phases = np.sort(np.angle(np.linalg.eigvals(loop)))
    return phases


def _grid(spec):
    shape = [int(x) for x in spec.get("grid_shape", [9, 9, 9])]
    if len(shape) != 3 or any(n < 2 for n in shape):
        raise ValueError("grid_shape must contain three integers >=2")
    bounds = np.asarray(
        spec.get("fractional_bounds", [[-0.5, 0.5], [-0.5, 0.5], [-0.5, 0.5]]),
        float,
    )
    if bounds.shape != (3, 2) or np.any(bounds[:, 0] >= bounds[:, 1]):
        raise ValueError("fractional_bounds must be increasing 3x2")
    axes = [
        np.linspace(bounds[i, 0], bounds[i, 1], shape[i], endpoint=False)
        for i in range(3)
    ]
    return shape, axes


def analyze(hr_path, metadata_path, spec_path, output_npz, receipt_path=None):
    if w90 is None or diag3d is None:
        raise RuntimeError("Co1/4TaSe2 Wannier consumers must be importable")
    hr_path = Path(hr_path)
    metadata_path = Path(metadata_path)
    spec_path = Path(spec_path)
    meta = json.loads(metadata_path.read_text())
    spec = json.loads(spec_path.read_text())

    if meta.get("soc_included") is not True or meta.get("exchange_included") is not True:
        raise ValueError("material artifact must explicitly declare SOC and exchange")
    source_identity = str(meta.get("source_identity", "")).strip()
    if not source_identity:
        raise ValueError("source_identity required")

    num_wann, rv, hb, deg = w90._load_hr(hr_path)
    selected = [int(x) for x in spec.get("selected_bands", [])]
    gap_floor = float(spec.get("external_gap_floor_ev", 1e-6))
    shape, axes = _grid(spec)
    curvature = np.empty((*shape, 3), float)
    external_gap = np.empty(shape, float)

    for ix, kx in enumerate(axes[0]):
        for iy, ky in enumerate(axes[1]):
            for iz, kz in enumerate(axes[2]):
                h, derivs = diag3d.h_and_derivs_fractional(
                    np.array([kx, ky, kz]), rv, hb, deg
                )
                evals, evecs = np.linalg.eigh(h)
                _, _, gap = projector_and_derivatives(
                    evals, evecs, derivs, selected, gap_floor=gap_floor
                )
                curvature[ix, iy, iz] = subspace_curvature_vector(
                    evals, evecs, derivs, selected, gap_floor=gap_floor
                )
                external_gap[ix, iy, iz] = gap

    loop_receipts = []
    for loop_spec in spec.get("wilson_loops", []):
        name = str(loop_spec.get("name", "unnamed-loop"))
        points = np.asarray(loop_spec.get("points_fractional", []), float)
        if points.ndim != 2 or points.shape[1] != 3 or points.shape[0] < 3:
            raise ValueError(f"Wilson loop {name} must provide >=3 fractional-k points")
        frames = []
        gaps = []
        for k in points:
            h, _ = diag3d.h_and_derivs_fractional(k, rv, hb, deg)
            evals, evecs = np.linalg.eigh(h)
            frame, gap = subspace_frame(evals, evecs, selected, gap_floor=gap_floor)
            frames.append(frame)
            gaps.append(gap)
        phases = wilson_loop_phases(frames)
        loop_receipts.append({
            "name": name,
            "point_count": int(points.shape[0]),
            "eigenphases_rad": phases.tolist(),
            "minimum_external_gap_ev": float(min(gaps)),
            "claim_role": "COMPUTED",
        })

    np.savez_compressed(
        output_npz,
        kx_fractional=axes[0],
        ky_fractional=axes[1],
        kz_fractional=axes[2],
        subspace_curvature_fractional=curvature,
        external_gap_ev=external_gap,
        selected_bands=np.asarray(selected, int),
    )

    provenance = {}
    for label, path in (("hr", hr_path), ("metadata", metadata_path), ("spec", spec_path)):
        provenance[label + "_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()

    receipt = {
        "source_identity": source_identity,
        "selected_bands": selected,
        "grid_shape": shape,
        "minimum_external_gap_ev": float(np.min(external_gap)),
        "maximum_curvature_norm_fractional": float(
            np.max(np.linalg.norm(curvature, axis=-1))
        ),
        "wilson_loops": loop_receipts,
        "provenance": provenance,
        "output_npz": str(output_npz),
        "attribution": {
            "material_artifact": "ACQUIRED/EXTERNAL COMPUTATIONAL ARTIFACT",
            "projector_curvature": "COMPUTED",
            "wilson_loop_spectrum": "COMPUTED",
            "formal_contract": "FORMAL",
            "material_topology_interpretation": "INFERRED only after same-object validation",
        },
        "epistemic_boundary": (
            "degeneracy-safe only for a selected subspace isolated from its complement; "
            "this receipt does not establish the validity of the supplied material Hamiltonian, "
            "does not convert family-level topology into a CoTa4Se8 observation, and does not "
            "compute metallic anomalous-Hall or spin-Hall conductivity"
        ),
    }
    if receipt_path:
        Path(receipt_path).write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("wannier90_hr_dat")
    parser.add_argument("metadata_json")
    parser.add_argument("topology_spec_json")
    parser.add_argument("output_npz")
    parser.add_argument("--receipt")
    args = parser.parse_args()
    print(json.dumps(analyze(
        args.wannier90_hr_dat,
        args.metadata_json,
        args.topology_spec_json,
        args.output_npz,
        args.receipt,
    ), indent=2))
