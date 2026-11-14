"""Crosswalk nonrelativistic spin-space generators to literal BNS 194.268 ops.

Sah et al. (npj Quantum Materials 11, 63 (2026), DOI
10.1038/s41535-026-00885-5) state that opposite-spin sublattices are exchanged
by M_z and the sixfold screw C_6z t, combined in spin-space notation with a pi
spin rotation [C2 || M_z] and [C2 || C_6z t].

The relativistic magnetic-space-group table uses antiunitary tagging instead.
This script checks that the corresponding crystallographic coordinate maps are
literally present among the antiunitary BNS 194.268 operations.  It does NOT
identify the spin-space and magnetic-space-group representations as the same
representation in the SOC case.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

TARGETS = {
    "mirror_Mz_layer_exchange": "x,y,-z+1/2",
    "sixfold_screw_C6z_t_layer_exchange": "x-y,x,z+1/2",
}


def audit(path):
    data = json.loads(Path(path).read_text())
    if data.get("bns_number") != "194.268":
        raise ValueError("expected BNS 194.268 authority table")
    ops = {(o["triplet"], bool(o["antiunitary"])) for o in data["operations"]}
    result = {}
    for name, triplet in TARGETS.items():
        result[name] = {
            "triplet": triplet,
            "antiunitary_present": (triplet, True) in ops,
            "unitary_present": (triplet, False) in ops,
        }
        if not result[name]["antiunitary_present"]:
            raise AssertionError(f"missing expected antiunitary generator {triplet}")
    return {
        "source_bns_authority": data.get("authority"),
        "bns_number": data["bns_number"],
        "bns_symbol": data["bns_symbol"],
        "sah_source_doi": "10.1038/s41535-026-00885-5",
        "targets": result,
        "status": "literal crystallographic generator maps identified in BNS table",
        "epistemic_boundary": (
            "coordinate-map crosswalk only: nonrelativistic spin-space pi-spin "
            "rotation and relativistic antiunitary MSG representations are not "
            "declared representation-identical, especially once SOC is present"
        ),
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("bns_json")
    p.add_argument("--receipt")
    args = p.parse_args()
    out = audit(args.bns_json)
    if args.receipt:
        Path(args.receipt).write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))
