#!/usr/bin/env python3
"""Selected ordinary SU2 Witten mod-two checks in source K=ker(Chi33).

Original physical representation/chiral parity E6 #1106 / KK #1241.
Source states imported from existing gs_anomaly_factor; Higgs K via
original pi1 quotient test. Classical original result: E. Witten,
'An SU(2) Anomaly', Phys Lett B 117 (1982) 324–328,
DOI 10.1016/0370-2693(82)90728-6. New source-specific finite
count by Johl Brown / OpenAI ChatGPT-assisted implementation.

For an ordinary spin 4D SU2 gauge subgroup, an ODD number of
isospin-1/2 Weyl multiplets has the mod2 anomaly. RH doublets count
too: SU2 fundamental is pseudoreal. Actual K retains SU2L×SU2R
since their determinants equal one. This does not classify spin
bordism Omega5^Spin(BK), correlated U1/quotient sectors, eta phases
or the all-field 5D orbifold.
"""
from pathlib import Path
from contextlib import redirect_stdout
import runpy
import io

ROOT=Path(__file__).resolve().parents[1]
def owner(rel,keys):
    out=io.StringIO()
    with redirect_stdout(out):
        v=runpy.run_path(str(ROOT/rel))
    assert "PASS" in out.getvalue()
    assert all(k in v for k in keys)
    return v
prior=owner("scripts/check_kk_e6_orbifold_gs_anomaly_factor.py",("states","P"))
top=owner("scripts/check_kk_e6_h_pi1_charge_deck.py",("chi_degree","A","R"))
assert top["chi_degree"](top["R"])==0
# Original source states enumerated as 9 A, 9 B, 9 C states;
# A: (3c,bar3L), B: (bar3c,3R), C: (3L,bar3R).
states=prior["states"]
assert len(states)==27
A,B,C=states[:9],states[9:18],states[18:]
assert all(x["c"]==1 for x in A)
assert all(x["c"]==-1 for x in B)
assert all(x["c"]==0 for x in C)
# Each SU2 doublet contains two weights with equal chirality and a
# multiplicity index; verify rather than double-counting both weights.
L=[]
for color in range(3):
    left,right=A[3*color],A[3*color+1]
    assert left["l"]==0 and right["l"]==1
    assert left["sign"]==right["sign"]
    L.append(left["sign"])
for r in range(3):
    left,right=C[r],C[3+r]
    assert left["l"]==0 and right["l"]==1
    assert left["r"]==right["r"]==r
    assert left["sign"]==right["sign"]
    L.append(left["sign"])
R=[]
for color in range(3):
    left,right=B[3*color],B[3*color+1]
    assert left["r"]==0 and right["r"]==1
    assert left["sign"]==right["sign"]
    R.append(left["sign"])
for l in range(3):
    left,right=C[3*l],C[3*l+1]
    assert left["r"]==0 and right["r"]==1
    assert left["l"]==right["l"]==l
    assert left["sign"]==right["sign"]
    R.append(left["sign"])
assert L==R==[1,1,1,-1,-1,1]
for name,v in (("SU2L",L),("SU2R",R)):
    assert len(v)==6 and v.count(+1)==4 and v.count(-1)==2
    assert len(v)%2==0 and sum(v)%2==0
    print(f"PASS {name}: four LH + two RH fundamental doublets, ordinary mod2=0")
print("PASS source-based Witten SU2 fundamental checks for selected K subgroups")
print("OPEN other global eta/spin quotient anomaly, full 5D determinant and WZ zeros")
