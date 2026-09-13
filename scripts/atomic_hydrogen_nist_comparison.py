#!/usr/bin/env python3
"""Compare the committed repaired hydrogenic 1s energy to NIST ASD H I.

This is a diagnostic reference-data comparison, not a claim that the infinite-
nuclear-mass nonrelativistic hydrogenic model equals measured hydrogen.
"""

import argparse
import hashlib
import json
from pathlib import Path

HARTREE_EV_2022_CODATA = 27.211386245981
NIST_HI_IE_EV = 13.598434599702
NIST_HI_IE_UNCERTAINTY_EV = 0.000000000012


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--radial-receipt",
        type=Path,
        default=Path(
            "Artifacts/atomic-periodic-table-369/"
            "radial-identity-repair-receipt.json"
        ),
    )
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    radial = json.loads(args.radial_receipt.read_text())
    one_s = next(s for s in radial["states"] if s["n"] == 1 and s["l"] == 0)

    numeric_ie_ev = -one_s["energy_hartree"] * HARTREE_EV_2022_CODATA
    infinite_mass_analytic_ie_ev = 0.5 * HARTREE_EV_2022_CODATA

    receipt = {
        "producer": "scripts/atomic_hydrogen_nist_comparison.py",
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "input_radial_receipt": str(args.radial_receipt),
        "input_radial_producer_sha256": radial["producer_sha256"],
        "model": "nonrelativistic infinite-nuclear-mass Coulomb hydrogenic Z=1",
        "hartree_to_ev_2022_codata": HARTREE_EV_2022_CODATA,
        "nist_asd_doi": "10.18434/T4W30F",
        "nist_spectrum": "H I",
        "nist_ground_shell": "1s",
        "nist_ionization_energy_ev": NIST_HI_IE_EV,
        "nist_uncertainty_ev": NIST_HI_IE_UNCERTAINTY_EV,
        "numeric_1s_energy_hartree": one_s["energy_hartree"],
        "numeric_ionization_energy_ev": numeric_ie_ev,
        "numeric_minus_nist_ev": numeric_ie_ev - NIST_HI_IE_EV,
        "numeric_relative_residual": (numeric_ie_ev - NIST_HI_IE_EV) / NIST_HI_IE_EV,
        "analytic_infinite_mass_ionization_energy_ev": infinite_mass_analytic_ie_ev,
        "analytic_infinite_mass_minus_nist_ev": (
            infinite_mass_analytic_ie_ev - NIST_HI_IE_EV
        ),
        "diagnostic": (
            "The direct NIST residual mixes discretization error with physical "
            "model incompleteness. The analytic infinite-mass Coulomb value is "
            "also retained so accidental cancellation cannot be promoted as accuracy."
        ),
        "next_physics": [
            "finite proton mass / reduced-mass correction",
            "relativistic and QED corrections if pursuing hydrogen precision",
            "many-electron SCF/HF/exchange treatment for Z>1",
        ],
        "passed": radial["passed"] is True,
        "non_promotion_boundary": (
            "This comparison pays only a one-electron reference-data diagnostic. "
            "It does not validate the many-electron periodic-table mechanism."
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
