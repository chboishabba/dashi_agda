#!/usr/bin/env python3
"""Golden-ratio and geometric-resummation diagnostics for the CKM lane."""

from __future__ import annotations

import json
import math


ALPHA1 = 0.041240
PDG_A_TARGET = 0.826
PDG_VCB_TARGET = 0.0408
PDG_VUB_TARGET_LOW = 0.00357
PDG_VUB_TARGET = 0.00369


def main() -> None:
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    a_base = 112.0 / (9.0 * math.pi * math.sqrt(24.0))
    first_order_factor = 1.0 + ALPHA1 / 2.0
    geometric_factor = 1.0 / (1.0 - ALPHA1 / 2.0)
    a_first = a_base * first_order_factor
    a_geometric = a_base * geometric_factor

    y23_base = 14.0 / math.sqrt(24.0) * (8.0 * math.pi / 3.0)
    vcb_base = ALPHA1**2 * y23_base
    vcb_geometric = ALPHA1**2 * y23_base * geometric_factor

    y13_bridge = 24.0 * math.pi / math.sqrt(6.0)
    y13_phi = phi * y13_bridge
    required_y13_low = PDG_VUB_TARGET_LOW / ALPHA1**3
    required_y13 = PDG_VUB_TARGET / ALPHA1**3

    diagnostics = {
        "alpha1": ALPHA1,
        "phi": phi,
        "base_A": a_base,
        "first_order_factor": first_order_factor,
        "geometric_factor": geometric_factor,
        "first_order_A": a_first,
        "geometric_A": a_geometric,
        "pdg_A_target": PDG_A_TARGET,
        "geometric_A_relative_error": (a_geometric - PDG_A_TARGET) / PDG_A_TARGET,
        "base_Vcb": vcb_base,
        "geometric_Vcb": vcb_geometric,
        "pdg_Vcb_target": PDG_VCB_TARGET,
        "geometric_Vcb_relative_error": (vcb_geometric - PDG_VCB_TARGET)
        / PDG_VCB_TARGET,
        "y13_bridge": y13_bridge,
        "y13_phi": y13_phi,
        "pdg_Vub_target_low": PDG_VUB_TARGET_LOW,
        "required_y13_for_Vub_low": required_y13_low,
        "required_y13_low_over_bridge": required_y13_low / y13_bridge,
        "required_y13_low_over_phi_bridge": required_y13_low / y13_phi,
        "pdg_Vub_target": PDG_VUB_TARGET,
        "required_y13_for_Vub": required_y13,
        "required_y13_over_bridge": required_y13 / y13_bridge,
        "required_y13_over_phi_bridge": required_y13 / y13_phi,
        "flags": {
            "vcbGeometricResummationDiagnostic": True,
            "y13GoldenRatioDiagnostic": True,
            "physicalCKMPromoted": False,
            "physicalVubPromoted": False,
        },
    }
    print(json.dumps(diagnostics, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
