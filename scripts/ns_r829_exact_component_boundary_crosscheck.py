#!/usr/bin/env python3
"""Check the real R829 exact Fourier component evaluator against the R829D boundary.

Execute the existing independent component producer rather than copying its
results or inventing an Agda proof. The output is a falsifiable cross-check,
not a kernel-certified same-object weld.
"""
import ast
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PRODUCER=ROOT/"scripts/check_ns_r829_rational_345_component_certificate.py"
BOUNDARY=ROOT/"DASHI/Physics/Closure/NSTriadKNR650Rational345RepositoryVectorBoundaryRound829Exact.agda"
EXPECTED_MODES=((-3,-4,0),(-3,0,0),(-3,4,0),(0,-4,0),(0,4,0),(3,-4,0),(3,0,0),(3,4,0))
EXPECTED_WORK=(Fraction(-48),Fraction(322917,250),Fraction(-48),Fraction(-428272,125),
               Fraction(-428272,125),Fraction(-48),Fraction(322917,250),Fraction(-48))
def check(rows,source):
    if rows.get("schema")!="ns_r829_rational_345_component_certificate_v1":
        raise ValueError("wrong exact component producer")
    if rows.get("repository_agda_reification_complete") is not False:
        raise ValueError("unverified promotion in producer")
    if source.count("Work.fixedOutputMixedProduct S")!=8 or source.count("Work.fixedOutputCommutator S")!=8:
        raise ValueError("R829D no longer has exactly eight selected operator equations")
    import re
    for index in range(1,9):
        match=re.search(r"(?m)^k"+str(index).translate(str.maketrans("12345678","₁₂₃₄₅₆₇₈"))+r"\s*=\s*Z3.mode",source)
        if match is None:
            raise ValueError(f"missing physical mode k{index} in R829D")
    outputs=rows.get("output_rows",{})
    works=[]
    for k in EXPECTED_MODES:
        row=outputs.get(str(k))
        if row is None:
            raise ValueError(f"missing same-output Fourier mode {k}")
        works.append(Fraction(row["coherent_work"]))
    if tuple(works)!=EXPECTED_WORK:
        raise ValueError(f"finite Fourier work differs from R829D literals: {works}")
    totals=rows.get("totals",{})
    if sum(works)!=Fraction(totals["coherent_work"]) or sum(works)!=Fraction(-557627,125):
        raise ValueError("selected eight work values do not reproduce total")
    if Fraction(totals["canonical_signed_rate"])!=Fraction(-28273644,125):
        raise ValueError("canonical R815 normalization differs")
    return {"schema":"dashi.ns.r829_same_output_crosscheck.v1",
            "checked_modes":[list(k) for k in EXPECTED_MODES],
            "eight_exact_work_values":[str(x) for x in works],
            "coherent_work_total":str(sum(works)),
            "status":"independent symbolic arithmetic matches selected R829D scalar outputs",
            "repository_native_vector_equalities_kernel_checked":False,
            "physical_R408_real_ode_weld_certified":False,
            "clay_promotion":False}
def main():
    raw=subprocess.check_output([sys.executable,str(PRODUCER)],cwd=ROOT,text=True)
    result=check(json.loads(raw),BOUNDARY.read_text())
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=="__main__":
    main()
