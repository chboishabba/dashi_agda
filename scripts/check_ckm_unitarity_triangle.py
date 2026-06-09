#!/usr/bin/env python3
"""Compute the diagnostic CKM unitarity-triangle apex from current carrier inputs."""

from __future__ import annotations

import json
import math

ALPHA1 = 0.041240
PHI = (1.0 + math.sqrt(5.0)) / 2.0
LAMBDA = ALPHA1 * math.pi * math.sqrt(3.0)
A_WOLFENSTEIN = 0.8255982974316682
DELTA29 = math.atan2(2.0 * math.sqrt(7.0), 1.0) - math.atan2(2.0, 5.0)
Y13_CANDIDATE = PHI * 14.0 / (1.0 - ALPHA1 / 2.0) * (8.0 * math.pi / 3.0) / math.sqrt(24.0)
VUB_ABS = ALPHA1**3 * Y13_CANDIDATE

PDG_RHOBAR_BEST_FIT_APPROX = 0.145
PDG_ETABAR_BEST_FIT_APPROX = 0.343


def main() -> None:
    ru = VUB_ABS / (A_WOLFENSTEIN * LAMBDA**3)
    rhobar = ru * math.cos(DELTA29)
    etabar = ru * math.sin(DELTA29)
    distance_to_pdg = math.hypot(
        rhobar - PDG_RHOBAR_BEST_FIT_APPROX,
        etabar - PDG_ETABAR_BEST_FIT_APPROX,
    )

    diagnostics = {
        "inputs": {
            "Vub_abs": VUB_ABS,
            "lambda": LAMBDA,
            "A": A_WOLFENSTEIN,
            "delta29_radians": DELTA29,
            "y13_candidate": Y13_CANDIDATE,
        },
        "formula": "Ru = |Vub|/(A*lambda^3); rhobar = Ru*cos(delta29); etabar = Ru*sin(delta29)",
        "computed": {
            "Ru": ru,
            "rhobar": rhobar,
            "etabar": etabar,
            "distance_to_pdg_best_fit_approx": distance_to_pdg,
        },
        "pdg_best_fit_qualitative": {
            "rhobar_approx": PDG_RHOBAR_BEST_FIT_APPROX,
            "etabar_approx": PDG_ETABAR_BEST_FIT_APPROX,
            "comparison": "carrier apex has rho near the PDG-sized comparison and eta low under the current phase/Vub convention",
        },
        "paper6_diagnostic_table": [
            ["input |Vub|", VUB_ABS, "current phi*14 geometric diagnostic"],
            ["input lambda", LAMBDA, "carrier Wolfenstein lambda diagnostic"],
            ["input A", A_WOLFENSTEIN, "carrier Wolfenstein A diagnostic"],
            ["input delta29", DELTA29, "carrier phase diagnostic"],
            ["derived Ru", ru, "|Vub|/(A*lambda^3)"],
            ["derived rhobar", rhobar, "PDG-sized comparison about 0.145"],
            ["derived etabar", etabar, "PDG-sized comparison about 0.343"],
        ],
        "paper6_figure_plan": [
            "plot PDG-sized apex near (0.145, 0.343)",
            "plot carrier apex near (0.160, 0.251)",
            "draw Ru ray at delta29",
            "label the eta undershoot as a phase/Vub diagnostic gap",
        ],
        "flags": {
            "rhobarEtabarComputed": True,
            "unitarityTriangleDiagnosticRecorded": True,
            "pdgQualitativeComparisonRecorded": True,
            "paper6FigurePlanRecorded": True,
            "physicalUnitarityTrianglePromoted": False,
            "physicalCPPromoted": False,
            "physicalCKMPromoted": False,
        },
    }
    print(json.dumps(diagnostics, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
