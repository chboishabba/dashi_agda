#!/usr/bin/env python3
"""Extract Vub, Vtd, and Jarlskog from the current full CKM diagnostic."""

from __future__ import annotations

import json
import numpy as np

from check_ckm_from_physical_mass_matrix import VEV_GEV, full_yukawa_matrix


def main() -> None:
    md = full_yukawa_matrix() * (VEV_GEV / np.sqrt(2.0))
    _, ud = np.linalg.eigh(md.conj().T @ md)
    v = ud
    abs_v = np.abs(v)
    j = np.imag(v[0, 1] * v[1, 2] * np.conj(v[0, 2]) * np.conj(v[1, 1]))

    diagnostics = {
        "Vub_abs": float(abs_v[0, 2]),
        "Vtd_abs": float(abs_v[2, 0]),
        "Jarlskog": float(j),
        "Jarlskog_abs": float(abs(j)),
        "pdg_Jarlskog_target": 3.08e-5,
        "J_over_PDG_abs": float(abs(j) / 3.08e-5),
        "flags": {
            "jarlskogInvariantComputed": True,
            "cpViolationDiagnosticRecorded": True,
            "physicalCPPhaseDerived": False,
            "physicalCKMPromoted": False,
        },
    }
    print(json.dumps(diagnostics, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
