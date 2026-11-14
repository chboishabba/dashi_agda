#!/usr/bin/env python3
"""Source geometry and published DFT benchmark negative controls.

Zhao et al., arXiv:2506.22408 v1, §VI.9.2 (XYZ), §VI.6 Table 8.
These published reference numbers are NOT recomputed DFT or AFQMC receipts.
"""
import json
from qcafqmc_nickel41_integrals import geometry_receipts

REFERENCE_EH={
 "PBE0":{"B":-2743.0559,"BC":-2742.9552,"C":-2743.0313},
 "B3LYP":{"B":-2744.1221,"BC":-2744.0196,"C":-2744.0947},
 "M06-2X":{"B":-2744.0356,"BC":-2743.9444,"C":-2744.0287},
 "wB97X":{"B":-2744.0981,"BC":-2743.9880,"C":-2744.0688}}
PUBLISHED_KCAL={
 "PBE0":{"BC":63.20,"C":15.49},
 "B3LYP":{"BC":64.35,"C":17.21},
 "M06-2X":{"BC":57.23,"C":4.37},
 "wB97X":{"BC":69.08,"C":18.39}}
HARTREE_TO_KCAL=627.5094740631
def verify():
    geo=geometry_receipts()
    expected={"Ni":1,"P":2,"C":13,"O":1,"H":24}
    for key,receipt in geo.items():
        if receipt["element_counts"]!=expected:
            raise AssertionError(key+" source composition mismatch")
        assert receipt["sum_nuclear_charge"]==168
        assert receipt["atoms"]==41
    derived={}
    for method,energy in REFERENCE_EH.items():
        derived[method]={}
        for key in ("BC","C"):
            computed=(energy[key]-energy["B"])*HARTREE_TO_KCAL
            discrepancy=computed-PUBLISHED_KCAL[method][key]
            # Authors' absolute energies rounded to 4 decimals, hence
            # reaction energy from the printed table differs by ~0.06 kcal.
            assert abs(discrepancy)<0.07, (method,key,discrepancy)
            derived[method][key]={"rounded_table_delta_kcal":computed,
                  "printed_reference_delta_kcal":PUBLISHED_KCAL[method][key],
                  "rounding_delta_kcal":discrepancy}
    assert len({str(geo[k]["sha256"]) for k in geo})==3
    return {"scope":"source geometry + published rounded DFT table regression",
            "geometry":geo,"reference_deltas":derived,
            "ab_initio_DFT_executed":False,
            "author_charge_spin_verified":False,
            "passed":True}
if __name__=="__main__":
    print(json.dumps(verify(),indent=2))
