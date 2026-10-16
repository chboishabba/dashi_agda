#!/usr/bin/env python3
"""Source-bounded QTM matrix-element observer on DASHI's BM plane-wave model.

Xiao et al. Nature 653 (2026), DOI 10.1038/s41586-026-10378-x, compare the
flat-band QTM intensity with A(k,w) * P_t(k) * P_s(k), where P_t is top-layer
weight and P_s = <I + sigma_x> carries sublattice information. Their reported
best BM ratio is w0/w1=0.6.

This script evaluates only the wavefunction matrix-element factor P_t*P_s for
the central conduction band of the DASHI BM numerical model. It does not use
raw QTM data, electrostatic conversion, probe spectral functions, lifetime
broadening, or an interacting self-energy, so it is not an experimental fit.
"""

from __future__ import annotations
import hashlib
import json
from pathlib import Path
import numpy as np
import matbg_bm_plane_wave_replay as BM

THETA_DEG = 1.10
W_AB_EV = 0.11
RATIO = 0.6
SHELLS = 3


def observer_at(q: float):
    prepared = BM.prepare(THETA_DEG, SHELLS, W_AB_EV, RATIO)
    b1 = prepared[3]
    layer1 = prepared[5]
    k = q * b1
    h = BM.hamiltonian(k, THETA_DEG, prepared)
    values, vectors = np.linalg.eigh(h)
    mid = len(values) // 2
    state = vectors[:, mid]

    top_dim = 2 * len(layer1)
    top = state[:top_dim]
    pt = float(np.vdot(top, top).real)

    ps_weighted = 0.0
    for i in range(len(layer1)):
        a, b = top[2*i:2*i+2]
        ps_weighted += float(abs(a + b) ** 2)
    ps_conditional = ps_weighted / pt if pt > 0 else 0.0
    matrix_element_factor = pt * ps_conditional

    return {
        "q_along_b1": q,
        "energy_eV": float(values[mid]),
        "top_layer_weight_Pt": pt,
        "conditional_sublattice_Ps": ps_conditional,
        "Pt_times_Ps": matrix_element_factor,
    }


def main():
    qs = [0.0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1.0]
    rows = [observer_at(q) for q in qs]

    assert all(0.0 <= r["top_layer_weight_Pt"] <= 1.0 + 1e-12 for r in rows)
    assert all(r["conditional_sublattice_Ps"] >= -1e-12 for r in rows)
    factors = [r["Pt_times_Ps"] for r in rows]
    assert max(factors) - min(factors) > 1e-3

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/matbg_qtm_matrix_element_observer.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "source_doi": "10.1038/s41586-026-10378-x",
        "model_source_doi": "10.1073/pnas.1108174108",
        "theta_deg_fixture": THETA_DEG,
        "wAB_eV_generic_reference": W_AB_EV,
        "w0_over_w1_source_ratio": RATIO,
        "shells": SHELLS,
        "observer": "central-conduction-band wavefunction factor Pt(k)*Ps(k), with Ps from I+sigma_x on the selected top-layer component",
        "samples": rows,
        "factor_min": min(factors),
        "factor_max": max(factors),
        "assertions_passed": True,
        "promotion_boundaries": {
            "raw_qtm_data_used": False,
            "qtm_electrostatics_replayed": False,
            "probe_spectral_function_replayed": False,
            "interacting_self_energy": False,
            "experimental_fit": False,
            "same_sample_entropy": False,
            "agda_kernel_receipt": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
