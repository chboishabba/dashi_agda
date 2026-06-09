#!/usr/bin/env python3
"""Check the g12 isogeny normalization numerical diagnostic.

This is a numerical governance script, not a proof.  It records why the older
alpha1*g12 Cabibbo parametrisation is retained only as diagnostic history.
The active computation keeps the raw sqrt(3)/2 isogeny factor and the exact
X0(4) modular-volume factor 2*pi, then applies the alpha1 readback
sqrt(2.16/1270).  The sector normalization is now receipted by
U1CMOrbitIntegralReceipt; the remaining formal work is physical CKM
diagonalisation and PDG authority binding.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


ORBIT_NUMERATOR = 2.16
ORBIT_DENOMINATOR = 1270.0
PDG_VUS_TARGET = 0.2245


def main() -> None:
    raw_g12 = math.sqrt(3.0) / 2.0
    angular_factor = 2.0 * math.pi
    normalized_g12 = angular_factor * raw_g12
    orbit_integral_scale = math.sqrt(ORBIT_NUMERATOR / ORBIT_DENOMINATOR)
    diagnostic_vus = normalized_g12 * orbit_integral_scale
    absolute_error = abs(diagnostic_vus - PDG_VUS_TARGET)
    relative_error = absolute_error / PDG_VUS_TARGET

    report = {
        "pdg_vus_target": PDG_VUS_TARGET,
        "orbit_integral_numerator": ORBIT_NUMERATOR,
        "orbit_integral_denominator": ORBIT_DENOMINATOR,
        "orbit_integral_scale": orbit_integral_scale,
        "raw_isogeny_g12": raw_g12,
        "candidate_sector_angle_normalization": "vol(X0(4)) = 2*pi",
        "candidate_sector_angle_factor": angular_factor,
        "candidate_normalized_g12": normalized_g12,
        "active_computation": "pi*sqrt(3)*sqrt(2.16/1270)",
        "diagnostic_vus": diagnostic_vus,
        "diagnostic_absolute_error": absolute_error,
        "diagnostic_relative_error": relative_error,
        "open_formal_step": "physical CKM diagonalisation and PDG authority binding",
        "numerical_diagnostic": True,
        "normalization_derived": True,
        "cabibbo_angle_derived": False,
        "matches_pdg_promoted": False,
        "cabibbo_promotion": False,
    }

    output_path = Path("Docs/G12IsogenyNormalizationDiagnostic.md")
    output_path.write_text(
        "\n".join(
            [
                "# G12 Isogeny Normalization Diagnostic",
                "",
                "Date: `2026-05-29`",
                "Status: sector normalization derived; Cabibbo/CKM promotion still false",
                "",
                "The raw isogeny-degree factor remains explicit:",
                "",
                "```text",
                f"g12_raw = sqrt(3)/2 = {raw_g12:.12f}",
                "```",
                "",
                "The sector-angle normalization is the X0(4) modular volume:",
                "",
                "```text",
                "vol(X0(4)) = (pi/3)*psi(4) = (pi/3)*6 = 2*pi",
                f"g12_full = 2*pi*(sqrt(3)/2) = pi*sqrt(3) = {normalized_g12:.12f}",
                "```",
                "",
                "The active numerical computation is",
                "",
                "```text",
                f"alpha1 = sqrt(2.16/1270) = {orbit_integral_scale:.12f}",
                f"pi*sqrt(3)*sqrt(2.16/1270) = {diagnostic_vus:.12f}",
                f"PDG |V_us| comparison value = {PDG_VUS_TARGET:.12f}",
                f"absolute error = {absolute_error:.12f}",
                f"relative error = {100.0 * relative_error:.6f} percent",
                "```",
                "",
                "`U1CMOrbitIntegralReceipt` now derives the p2-p3 sector-angle",
                "normalization from vol(X0(4)).  This still does not promote the",
                "Cabibbo angle: physical CKM diagonalisation and accepted PDG",
                "authority binding remain open.",
                "",
                "Governance flags remain:",
                "",
                "```text",
                "sectorAngleNormalizationDerived = true",
                "angularNormalizedDiagnosticPromoted = true",
                "cabibboAngleDerived = false",
                "matchesPDG = false",
                "cabibboPromotion = false",
                "```",
                "",
                "JSON payload:",
                "",
                "```json",
                json.dumps(report, indent=2, sort_keys=True),
                "```",
                "",
            ]
        ),
        encoding="utf-8",
    )

    print(json.dumps(report, indent=2, sort_keys=True))
    print(f"report: {output_path}")


if __name__ == "__main__":
    main()
