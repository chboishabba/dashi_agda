#!/usr/bin/env python3
"""Gauge-invariant quantum-geometry diagnostic on the DASHI BM plane-wave model.

Uses the rank-two projector onto the central BM bands:
  g_ij = 1/2 Re Tr[(d_i P)(d_j P)]
  F_xy = Re[-i Tr(P [d_x P, d_y P])]
with finite differences in dimensionless q = k/k_theta coordinates.

The formula is standard band-geometry mathematics. 2026 moire-geometry papers
motivate the consumer, but they do not own or calibrate this MATBG calculation.
In particular Liu et al., Nat Commun 17, 8300 (2026),
DOI 10.1038/s41467-026-74848-6 concerns ATQG, not this MATBG sample.
"""

from __future__ import annotations
import hashlib
import json
from pathlib import Path
import numpy as np
import matbg_bm_plane_wave_replay as BM

DQ = 1.0e-3
THETA = 1.08
W_AB = 0.11
RATIO = 0.6


def central_projector(k, prepared):
    h = BM.hamiltonian(k, THETA, prepared)
    values, vectors = np.linalg.eigh(h)
    mid = len(values) // 2
    u = vectors[:, mid - 1:mid + 1]
    return u @ u.conj().T, values[mid - 1:mid + 1]


def geometry_at(qx: float, qy: float, shells: int):
    prepared = BM.prepare(THETA, shells, W_AB, RATIO)
    ktheta = prepared[1]
    k = ktheta * np.array([qx, qy])
    dx = ktheta * np.array([DQ, 0.0])
    dy = ktheta * np.array([0.0, DQ])

    p, energies = central_projector(k, prepared)
    pxp, _ = central_projector(k + dx, prepared)
    pxm, _ = central_projector(k - dx, prepared)
    pyp, _ = central_projector(k + dy, prepared)
    pym, _ = central_projector(k - dy, prepared)

    dpx = (pxp - pxm) / (2.0 * DQ)
    dpy = (pyp - pym) / (2.0 * DQ)

    gxx = 0.5 * np.real(np.trace(dpx @ dpx))
    gyy = 0.5 * np.real(np.trace(dpy @ dpy))
    gxy = 0.5 * np.real(np.trace(dpx @ dpy))
    berry = np.real(-1j * np.trace(p @ (dpx @ dpy - dpy @ dpx)))

    return {
        "qx": qx,
        "qy": qy,
        "shells": shells,
        "gxx": float(gxx),
        "gyy": float(gyy),
        "gxy": float(gxy),
        "trace_metric": float(gxx + gyy),
        "traced_berry_curvature": float(berry),
        "projector_idempotence_error": float(np.max(np.abs(p @ p - p))),
        "central_energies_eV": [float(x) for x in energies],
    }


def compact_geometry(row):
    return {
        "gxx": row["gxx"],
        "gyy": row["gyy"],
        "gxy": row["gxy"],
        "trace_metric": row["trace_metric"],
        "traced_berry_curvature": row["traced_berry_curvature"],
    }


def main():
    point = {str(n): geometry_at(0.2, 0.15, n) for n in (2, 3, 4)}

    scan = []
    for qx in np.linspace(0.05, 0.85, 5):
        for qy in np.linspace(0.05, 0.85, 5):
            scan.append(geometry_at(float(qx), float(qy), 3))
    hottest = max(scan, key=lambda row: row["trace_metric"])
    coolest = min(scan, key=lambda row: row["trace_metric"])

    assert max(v["projector_idempotence_error"] for v in point.values()) < 1e-12
    assert abs(point["4"]["trace_metric"] - point["3"]["trace_metric"]) < 1e-3
    assert abs(point["4"]["traced_berry_curvature"]) < 1e-8
    assert hottest["trace_metric"] > 10.0 * coolest["trace_metric"]

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/matbg_bm_quantum_geometry.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "execution_environment": "Python with numpy.linalg.eigh",
        "model": "rank-two central-band projector geometry on BM plane-wave model",
        "source_model": "10.1073/pnas.1108174108",
        "sota_inspiration_not_same_object": "10.1038/s41467-026-74848-6",
        "coordinate": "dimensionless q=k/k_theta",
        "finite_difference_dq": DQ,
        "reference_point_q": [0.2, 0.15],
        "shell_convergence": {key: compact_geometry(value) for key, value in point.items()},
        "coarse_scan_shell3": {
            "minimum_trace_metric": coolest["trace_metric"],
            "minimum_at_q": [coolest["qx"], coolest["qy"]],
            "maximum_trace_metric": hottest["trace_metric"],
            "maximum_at_q": [hottest["qx"], hottest["qy"]],
        },
        "assertions_passed": True,
        "promotion_boundaries": {
            "experimental_quantum_metric_calibration": False,
            "interacting_quantum_geometry": False,
            "same_sample_superconductivity": False,
            "chern_number_from_local_scan": False,
            "agda_kernel_receipt": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
