#!/usr/bin/env python3
"""Real original 2.Suz:2 ATLAS quotient -> repo-owned 729 Weil scalar replay.

Uses check_toe_atlas_mirror.C,D,J,P (their SHA-pinned original ATLAS
source matrix entries), NOT user-local Monster mmgroup C,D. Reuses the
earlier repo-owned toe_cyclotomic_operator.compile_shape kernel via
monster3b_original729_weil_source_cocycle_weld.

This proves a QUOTIENT-CHART donor with exact cyclotomic scalars:
 C,D have quotient orders 4,3; original ATLAS relator R^7=I.
 In the selected six-coordinate P polarization and scalar Δ^-rank:
 K0(C)=-1/3, K0(D)=K0(CDC^-1)=-1/27, K0(R)=-1/27,
 α(D,CDC^-1)=1, α(C,C)=1, K_R^7=I
 for BOTH ζ and ζ². Full Monster R^7=z does NOT follow from this
 script; it was reported separately using genuine mmgroup C,D.
 Never identify this ATLAS model's vacuum with MMV31 before transporting
 the original source symplectic intertwiner and confirming its phase.

No Magma, GAP, 196884D MM action or dense 729×729 matrix.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
from pathlib import Path
import argparse
import numpy as np
import check_toe_atlas_mirror as atlas
from monster3b_original729_weil_source_cocycle_weld import (
    I12,DELTA,ZETA,Q1,add,mul,power,inv,rootsix,k00,cocycle,
    f3_pow,word_matrix
)

def source_replay():
    P=atlas.P
    C=atlas.inv(P)@atlas.C@P%3
    D=atlas.inv(P)@atlas.D@P%3
    if not np.array_equal(f3_pow(C,2),2*I12%3):
        raise ValueError("wrong original ATLAS C4 quotient source")
    if not np.array_equal(f3_pow(D,3),I12):
        raise ValueError("wrong original ATLAS D3 quotient source")
    E=C@D@atlas.inv(C)%3
    R=word_matrix("cdcdcddcdd",C,D)
    if not np.array_equal(f3_pow(R,7),I12) or np.array_equal(R,I12):
        raise ValueError("wrong ATLAS source 10-letter R order7")
    results={"schema":"monster3b-authentic-ATLAS-2Suz2-729-Weil-scalar-source-v1",
       "original_source":"ATLAS 2.Suz:2 pinned GF3 generators via check_toe_atlas_mirror",
       "source_chart":"P symplectic basis of ATLAS form; Δ^-rank Weil model gauge",
       "source_Monster_word_attached":False,
       "original_actual_196884D_Monster_action_executed":False,
       "phases":{}}
    for phase in (1,2):
        vac={}
        for name,M,lam in [
            ("C",C,2),("D",D,1),("E",E,1),("DE",D@E%3,1),
            ("ED",E@D%3,1),("R",R,1)]:
            row=k00(M,lam,phase)
            if not row["k0_nonzero"]:
                raise AssertionError("original ATLAS source model zero-vacuum obstruction")
            vac[name]=row
        assert vac["C"]["k0_unitary_model_Qzeta3"]==["-1/3","0"]
        for label in ("D","E","DE","ED","R"):
            if vac[label]["k0_unitary_model_Qzeta3"]!=["-1/27","0"]:
                raise AssertionError(f"wrong original source vacuum {label}")
        pairs={}
        for name,A,la,B,lb in [("D_E",D,1,E,1),("E_D",E,1,D,1),
                               ("C_C",C,2,C,2)]:
            row=cocycle(A,la,B,lb,phase)
            if row["unitary_gauge_multiplier_Qzeta3"]!=["1","0"]:
                raise AssertionError(f"original source 729 pair scalar changed: {name}")
            pairs[name]=row
        current=R.copy()
        result=Q1
        staircase=[]
        for j in range(1,7):
            step=cocycle(R,1,current,1,phase)
            a,b=step["unitary_gauge_multiplier_Qzeta3"]
            scalar=(F(a),F(b))
            result=mul(result,scalar)
            staircase.append({"power":j+1,"scalar_Qzeta3":[a,b]})
            current=R@current%3
        if not np.array_equal(current,I12) or result!=Q1:
            raise AssertionError("original ATLAS 729 quotient relator has nontrivial R7")
        results["phases"][str(phase)]={
           "vacuum":vac,"pairs":pairs,
           "K_R7_equals_identity_in_selected_ATLAS_model":True,
           "K_R7_exact_scalar_Qzeta3":["1","0"],
           "R7_projective_staircase":staircase,
           "conditional_actual_Monster_R7_z_complement_relation":
              f"L_R,phase{phase}^7 = zeta^{phase*1%3} I90 only after actual 729 source weld"}
    return results
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out",type=Path,default=Path(
        ".dashi/monster3b-mmgroup/atlas729_source_relator.json"))
    a=p.parse_args()
    receipt=source_replay()
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("ATLAS_2SUZ2_WEIL729_K0_C_NEG_THIRD_D_E_NEG_TWENTYSEVENTH_R7_ONE_BOTH_PHASES")
    print("RECEIPT",a.out)
if __name__=="__main__":main()
