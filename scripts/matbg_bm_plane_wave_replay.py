#!/usr/bin/env python3
"""Independent reciprocal-lattice Bistritzer–MacDonald convergence receipt.

Scientific source:
  Bistritzer & MacDonald, PNAS 108 (2011), DOI 10.1073/pnas.1108174108.

External implementation cross-check:
  R-Carrasco/tbg-simulator (MIT), inspected for basis/cutoff conventions only.
  DASHI implementation below was written independently.

2026 source coordinate:
  Xiao et al., Nature 653 (2026), DOI 10.1038/s41586-026-10378-x,
  reports a BM wavefunction matrix-element comparison best fit w0/w1=0.6.

The 0.6 calculation below deliberately pairs that ratio with a generic
wAB=0.11 eV reference scale. It is NOT a same-sample Xiao calibration.
"""

from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import numpy as np

A_NM = 0.246
HBAR_VF = 2.1354 * A_NM
K_DIRAC = 4.0 * math.pi / (3.0 * A_NM)
SIGMA_X = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=complex)
SIGMA_Y = np.array([[0.0, -1.0j], [1.0j, 0.0]], dtype=complex)
IDENTITY_2 = np.eye(2, dtype=complex)


def geometry(theta_deg: float):
    theta = math.radians(theta_deg)
    ktheta = 2.0 * K_DIRAC * math.sin(theta / 2.0)
    q = ktheta * np.array([
        [0.0, -1.0],
        [math.sqrt(3.0) / 2.0, 0.5],
        [-math.sqrt(3.0) / 2.0, 0.5],
    ])
    return theta, ktheta, q, q[1] - q[0], q[2] - q[0]


def momentum_basis(theta_deg: float, shells: int):
    theta, ktheta, q, b1, b2 = geometry(theta_deg)
    center = 0.5 * q[0]
    radius = shells * np.linalg.norm(b1) + 1.0e-12
    bound = shells + 3
    layer1, layer2 = [], []
    for m in range(-bound, bound + 1):
        for n in range(-bound, bound + 1):
            g = m * b1 + n * b2
            if np.linalg.norm(g - center) <= radius:
                layer1.append((m, n))
            if np.linalg.norm(g + q[0] - center) <= radius:
                layer2.append((m, n))
    return theta, ktheta, q, b1, b2, layer1, layer2


def rotate_momentum(p: np.ndarray, angle: float):
    c, s = math.cos(angle), math.sin(angle)
    return np.array([c * p[0] + s * p[1], -s * p[0] + c * p[1]])


def dirac_block(p: np.ndarray, angle: float):
    pr = rotate_momentum(p, angle)
    return -HBAR_VF * (pr[0] * SIGMA_X + pr[1] * SIGMA_Y)


def tunnelling_matrices(w_ab: float, ratio: float):
    w_aa = ratio * w_ab
    matrices = []
    for j in range(3):
        phi = 2.0 * math.pi * j / 3.0
        matrices.append(
            w_aa * IDENTITY_2
            + w_ab * (math.cos(phi) * SIGMA_X + math.sin(phi) * SIGMA_Y)
        )
    return matrices


def prepare(theta_deg: float, shells: int, w_ab: float, ratio: float):
    theta, ktheta, q, b1, b2, layer1, layer2 = momentum_basis(theta_deg, shells)
    index2 = {mn: i for i, mn in enumerate(layer2)}
    offset = 2 * len(layer1)
    dimension = 2 * (len(layer1) + len(layer2))
    inter = np.zeros((dimension, dimension), dtype=complex)
    for i, (m, n) in enumerate(layer1):
        for matrix, shift in zip(tunnelling_matrices(w_ab, ratio),
                                 [(0, 0), (1, 0), (0, 1)]):
            destination = (m + shift[0], n + shift[1])
            if destination in index2:
                j = index2[destination]
                inter[offset + 2*j:offset + 2*j + 2, 2*i:2*i + 2] = matrix
    inter += inter.conj().T
    return theta, ktheta, q, b1, b2, layer1, layer2, inter


def hamiltonian(k: np.ndarray, theta_deg: float, prepared):
    theta, _, q, b1, b2, layer1, layer2, inter = prepared
    h = inter.copy()
    offset = 2 * len(layer1)
    for i, (m, n) in enumerate(layer1):
        p = k + m * b1 + n * b2
        h[2*i:2*i+2, 2*i:2*i+2] = dirac_block(p, -theta / 2.0)
    for i, (m, n) in enumerate(layer2):
        p = k + m * b1 + n * b2 + q[0]
        h[offset+2*i:offset+2*i+2, offset+2*i:offset+2*i+2] = dirac_block(
            p, theta / 2.0
        )
    return h


def central_bandwidth(theta_deg: float, shells: int, w_ab: float,
                      ratio: float, grid: int = 6):
    prepared = prepare(theta_deg, shells, w_ab, ratio)
    b1, b2 = prepared[3], prepared[4]
    dimension = prepared[-1].shape[0]
    mid = dimension // 2
    lower, upper = [], []
    hermiticity_error = 0.0
    for i in range(grid):
        for j in range(grid):
            k = (i / grid) * b1 + (j / grid) * b2
            h = hamiltonian(k, theta_deg, prepared)
            hermiticity_error = max(
                hermiticity_error, float(np.max(np.abs(h - h.conj().T)))
            )
            eig = np.linalg.eigvalsh(h)
            lower.append(float(eig[mid - 1]))
            upper.append(float(eig[mid]))
    return {
        "bandwidth_eV": max(upper) - min(lower),
        "lower_min_eV": min(lower),
        "upper_max_eV": max(upper),
        "dimension": dimension,
        "layer1_sites": len(prepared[5]),
        "layer2_sites": len(prepared[6]),
        "hermiticity_error": hermiticity_error,
    }


def compact_convergence(result):
    return {
        "bandwidth_eV": result["bandwidth_eV"],
        "dimension": result["dimension"],
        "hermiticity_error": result["hermiticity_error"],
    }


def main():
    xiao_convergence = {
        str(n): central_bandwidth(1.08, n, 0.11, 0.6)
        for n in (2, 3, 4)
    }
    relaxed_ratio = 0.0797 / 0.0975
    theta_values = np.arange(1.04, 1.1201, 0.005)
    sweep = [
        (float(theta), central_bandwidth(float(theta), 3, 0.0975, relaxed_ratio))
        for theta in theta_values
    ]
    best_theta, best_result = min(sweep, key=lambda item: item[1]["bandwidth_eV"])

    assert all(v["hermiticity_error"] < 1e-12 for v in xiao_convergence.values())
    assert abs(xiao_convergence["4"]["bandwidth_eV"]
               - xiao_convergence["3"]["bandwidth_eV"]) < 1e-4
    assert abs(best_theta - 1.085) < 0.006

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/matbg_bm_plane_wave_replay.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "execution_environment": "Python with numpy.linalg.eigvalsh",
        "model": "independent BM reciprocal-lattice plane-wave reconstruction",
        "sources": {
            "bm2011": "10.1073/pnas.1108174108",
            "xiao2026_ratio": "10.1038/s41586-026-10378-x",
            "external_implementation_crosscheck": "R-Carrasco/tbg-simulator (MIT)",
        },
        "xiao_ratio_reference_fixture": {
            "theta_deg": 1.08,
            "wAB_eV_generic_reference": 0.11,
            "wAA_over_wAB": 0.6,
            "same_sample_absolute_calibration": False,
            "convergence": {
                key: compact_convergence(value)
                for key, value in xiao_convergence.items()
            },
        },
        "relaxed_reference_crosscheck": {
            "wAA_eV": 0.0797,
            "wAB_eV": 0.0975,
            "shells": 3,
            "theta_step_deg": 0.005,
            "minimum_theta_deg": best_theta,
            "minimum_bandwidth_eV": best_result["bandwidth_eV"],
        },
        "assertions_passed": True,
        "promotion_boundaries": {
            "interacting_self_energy": False,
            "qtm_data_replay": False,
            "same_sample_entropy": False,
            "xiao_absolute_sample_calibration": False,
            "agda_kernel_receipt": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
