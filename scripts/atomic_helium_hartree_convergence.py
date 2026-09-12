#!/usr/bin/env python3
"""Grid-convergence diagnostic for the closed-shell helium Hartree producer.

This producer separates numerical discretization error from the physical
Hartree/HF approximation error.  It reuses atomic_helium_hartree_scf.py on a
sequence of doubled radial grids, compares against the published He Hartree--
Fock SCF limit, and retains a Pekeris nonrelativistic benchmark as a downstream
correlation coordinate.

No sequence/benchmark citation imports physical authority into DASHI.  The
purpose is to determine whether the remaining helium residual is mostly a
numerical defect or unpaid many-electron physics.
"""

import argparse
import hashlib
import json
from pathlib import Path

from atomic_helium_hartree_scf import (
    HARTREE_EV_2022_CODATA,
    NIST_HEI_IE_EV,
    run_helium_hartree,
)

HF_LIMIT_HARTREE = -2.861679995612
PEKERIS_NONREL_GROUND_HARTREE = -2.903724375
HF_LIMIT_DOI = "10.1016/0009-2614(92)85634-M"
PEKERIS_DOI = "10.1103/PhysRev.115.1216"
NIST_ASD_DOI = "10.18434/T4W30F"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    parser.add_argument(
        "--grids",
        type=int,
        nargs="+",
        default=[4000, 8000, 16000, 32000, 64000],
    )
    args = parser.parse_args()

    rows = []
    for npts in args.grids:
        r = run_helium_hartree(
            npts=npts,
            rmax=40.0,
            mixing=0.3,
            tolerance=1e-10,
            max_iterations=300,
        )
        rows.append(
            {
                "npts": npts,
                "total_energy_hartree": r["helium_total_energy_hartree"],
                "minus_hf_limit_hartree": (
                    r["helium_total_energy_hartree"] - HF_LIMIT_HARTREE
                ),
                "ionization_energy_ev": r["ionization_energy_ev"],
                "minus_nist_ev": r["ionization_energy_ev"] - NIST_HEI_IE_EV,
                "iterations": r["iterations"],
                "final_max_potential_delta": r["final_max_potential_delta"],
            }
        )

    coarse = rows[-2]["total_energy_hartree"]
    fine = rows[-1]["total_energy_hartree"]
    richardson_first_order = 2.0 * fine - coarse
    richardson_minus_hf = richardson_first_order - HF_LIMIT_HARTREE

    # Use exact nonrelativistic infinite-mass He+ = -2 Eh only for this
    # diagnostic extrapolation.  Finite nuclear mass / relativistic / QED
    # corrections remain outside this object.
    richardson_ie_hartree = -2.0 - richardson_first_order
    richardson_ie_ev = richardson_ie_hartree * HARTREE_EV_2022_CODATA

    correlation_gap_hartree = HF_LIMIT_HARTREE - PEKERIS_NONREL_GROUND_HARTREE

    monotone_to_hf = all(
        abs(rows[i + 1]["minus_hf_limit_hartree"])
        < abs(rows[i]["minus_hf_limit_hartree"])
        for i in range(len(rows) - 1)
    )

    receipt = {
        "producer": "scripts/atomic_helium_hartree_convergence.py",
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "upstream_producer": "scripts/atomic_helium_hartree_scf.py",
        "model": "restricted closed-shell spherical Hartree / RHF-equivalent He 1s2",
        "hf_limit_hartree": HF_LIMIT_HARTREE,
        "hf_limit_doi": HF_LIMIT_DOI,
        "pekeris_nonrel_ground_hartree": PEKERIS_NONREL_GROUND_HARTREE,
        "pekeris_doi": PEKERIS_DOI,
        "nist_asd_doi": NIST_ASD_DOI,
        "nist_helium_ie_ev": NIST_HEI_IE_EV,
        "rows": rows,
        "monotone_toward_hf_limit": monotone_to_hf,
        "richardson_first_order_total_energy_hartree": richardson_first_order,
        "richardson_minus_hf_limit_hartree": richardson_minus_hf,
        "richardson_ionization_energy_ev": richardson_ie_ev,
        "richardson_minus_nist_ev": richardson_ie_ev - NIST_HEI_IE_EV,
        "hf_minus_pekeris_hartree": correlation_gap_hartree,
        "hf_minus_pekeris_ev": correlation_gap_hartree * HARTREE_EV_2022_CODATA,
        "passed": bool(monotone_to_hf and abs(richardson_minus_hf) < 1e-4),
        "interpretation": (
            "The doubled-grid sequence converges toward the published helium HF/SCF "
            "limit.  Once discretization is extrapolated away, the remaining roughly "
            "1.14 eV separation from the accurate nonrelativistic helium ground-state "
            "benchmark is correlation/model error, not a radial-identity defect."
        ),
        "non_promotion_boundary": (
            "Agreement with the helium HF limit validates this finite Hartree producer "
            "against its approximation class.  It does not establish correlated helium, "
            "generic multi-orbital atoms, or empirical periodic-table recovery."
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
