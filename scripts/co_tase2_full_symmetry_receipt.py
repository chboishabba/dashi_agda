#!/usr/bin/env python3
"""Run the literal BNS 194.268 audit before the Bloch/sewing validation.

This is the preferred execution entry point for the symmetry lane because it
refuses to run the model receipt as a physical-group receipt unless the stored
independent MAGNDATA operation table is an exact same-object match first.
"""
import argparse
import json
from pathlib import Path

import co_tase2_bloch_symmetry as bloch
import co_tase2_bns_operation_audit as bns


def verify(authority_path):
    authority = bns.audit(authority_path)
    model = bloch.verify()
    return {
        "authority": authority,
        "bloch": model,
        "literal_bns_consumed_before_bloch_receipt": True,
        "material_hamiltonian_validated": False,
        "epistemic_boundary": (
            "Exact BNS operation-set identity and finite sewing/covariance tests "
            "are paid; the four-band H remains illustrative, not a DFT/Wannier "
            "Hamiltonian or quantitative ARPES fit."
        ),
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument(
        "authority_json",
        nargs="?",
        default="data/co_tase2/bns_194_268_magndata_operations.json",
    )
    p.add_argument("--receipt", default=None)
    a = p.parse_args()
    result = verify(a.authority_json)
    if a.receipt:
        Path(a.receipt).parent.mkdir(parents=True, exist_ok=True)
        Path(a.receipt).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
