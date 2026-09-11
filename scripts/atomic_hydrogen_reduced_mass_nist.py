#!/usr/bin/env python3
"""Apply the finite-proton-mass reduced-mass correction to hydrogen.

This continues the one-electron calibration snowball after the repaired radial
identity and first NIST comparison.  It deliberately keeps relativistic, recoil,
radiative/QED, finite-size and hyperfine corrections unpaid.
"""

import argparse
import hashlib
import json
from pathlib import Path

HARTREE_EV_2022_CODATA = 27.211386245981
ELECTRON_PROTON_MASS_RATIO_2022_CODATA = 5.446170214889e-4
NIST_HI_IE_EV = 13.598434599702
NIST_HI_IE_UNCERTAINTY_EV = 0.000000000012


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--comparison-receipt",
        type=Path,
        default=Path(
            "Artifacts/atomic-periodic-table-369/"
            "hydrogen-nist-comparison-receipt.json"
        ),
    )
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    upstream = json.loads(args.comparison_receipt.read_text())
    mu_over_me = 1.0 / (1.0 + ELECTRON_PROTON_MASS_RATIO_2022_CODATA)
    reduced_mass_ie_ev = 0.5 * HARTREE_EV_2022_CODATA * mu_over_me
    residual_ev = reduced_mass_ie_ev - NIST_HI_IE_EV

    receipt = {
        "producer": "scripts/atomic_hydrogen_reduced_mass_nist.py",
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "input_comparison_receipt": str(args.comparison_receipt),
        "input_comparison_producer_sha256": upstream["producer_sha256"],
        "model": "nonrelativistic Coulomb hydrogen with finite proton mass via reduced mass",
        "hartree_to_ev_2022_codata": HARTREE_EV_2022_CODATA,
        "electron_proton_mass_ratio_2022_codata": ELECTRON_PROTON_MASS_RATIO_2022_CODATA,
        "reduced_mass_over_electron_mass": mu_over_me,
        "reduced_mass_ionization_energy_ev": reduced_mass_ie_ev,
        "nist_asd_doi": "10.18434/T4W30F",
        "nist_ionization_energy_ev": NIST_HI_IE_EV,
        "nist_uncertainty_ev": NIST_HI_IE_UNCERTAINTY_EV,
        "reduced_mass_minus_nist_ev": residual_ev,
        "relative_residual": residual_ev / NIST_HI_IE_EV,
        "infinite_mass_minus_nist_ev": upstream[
            "analytic_infinite_mass_minus_nist_ev"
        ],
        "residual_magnitude_improves_over_infinite_mass": (
            abs(residual_ev) < abs(upstream["analytic_infinite_mass_minus_nist_ev"])
        ),
        "passed": upstream["passed"] is True,
        "unpaid_physics": [
            "relativistic fine-structure / Dirac corrections",
            "radiative QED corrections including Lamb shift",
            "higher-order recoil and proton finite-size effects",
            "many-electron SCF/HF/exchange/correlation for Z>1",
        ],
        "non_promotion_boundary": (
            "Reduced mass pays the leading finite-nuclear-mass correction only. "
            "The remaining NIST residual is not numerical failure evidence by itself "
            "and is not a periodic-table empirical validation."
        ),
    }

    text = json.dumps(receipt, indent=2, sort_keys=True)
    print(text)
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text + "\n", encoding="utf-8")
    raise SystemExit(0 if receipt["passed"] else 1)


if __name__ == "__main__":
    main()
