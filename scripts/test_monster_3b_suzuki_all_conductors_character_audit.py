#!/usr/bin/env python3
"""Standard-library exact tests for the all-conductors 6.Suz character audit.

Finite test group C2 x C3 x C5 is genuine; degree12/78 test rows are
reducible synthetic characters, *not* 6.Suz irreps or Monster evidence.
Original character arithmetic: Serre; source 6.Suz/Monster: BW 2007.
"""
import copy
from itertools import product
from math import gcd
import json
from monster_3b_suzuki_all_conductors_character_audit import Cyc,audit,phi_poly

def root(n,k):
    c=[0]*n;c[k%n]=1
    return Cyc.from_coeffs(n,c)

def wire(x):
    return {"conductor":x.n,
            "coefficients":[str(v) for v in x.v]+["0"]*(x.n-len(x.v))}

def run():
    for n in range(1,121):
        assert len(phi_poly(n))-1 == sum(gcd(k,n)==1 for k in range(1,n+1)),n
    for n in (3,5,7,11,15,21):
        z=root(n,1)
        assert z*z.conjugate()==1 and z==z.promote(2*n)
    G=list(product(range(2),range(3),range(5)))
    loc={x:i for i,x in enumerate(G)}
    char=lambda t,j,k: (root(3,j)*root(5,k))*(-1 if t else 1)
    a=[char(*g)*12 for g in G]
    pow2=[loc[(0,(2*j)%3,(2*k)%5)] for t,j,k in G]
    sq=[(x*x+a[pow2[i]])/2 for i,x in enumerate(a)]
    wrong=list(sq);wrong[12]=wrong[12]+1
    row=lambda name,values:{"label":name,"values":[wire(v) for v in values]}
    base={"table_id":"SYNTHETIC:C2xC3xC5",
          "class_orders":[(2 if t else 1)*(3 if j else 1)*(5 if k else 1)
                          for t,j,k in G],
          "power_map_2_zero_based":pow2,
          "central_c2_zero_based":loc[(1,0,0)],
          "central_c3_zero_based":loc[(0,1,0)],
          "degree12":[row("12",a)],
          "degree78":[row("direct",sq),
                      row("dual",[v.conjugate() for v in sq]),
                      row("altered",wrong)]}
    result=audit(base)
    matches={(x["78"],x["mode"]) for x in result["matches"]}
    assert ("direct","Sym2") in matches
    assert ("dual","dualSym2") in matches
    assert all(x[0]!="altered" for x in matches)
    assert any(x["78"]=="altered" and x["first_class"]==12
               for x in result["first_disagreements"])
    invalid=[{"table_id":"6.Suz"},
             {"power_map_2_zero_based":[0]*30},
             {"class_orders":[1]*30},
             {"central_c3_zero_based":1},
             {"group_order":77},
             {"degree12":[row("12",a),row("12",a)]}]
    accepted_bad=0
    for patch in invalid:
        sample=copy.deepcopy(base);sample.update(patch)
        try:audit(sample)
        except ValueError:continue
        accepted_bad+=1
    assert accepted_bad==0
    for broken in ({"conductor":9,"coefficients":["1","0"]},
                   {"conductor":5000,"coefficients":[0]*5000}):
        sample=copy.deepcopy(base)
        sample["degree78"][0]["values"][1]=broken
        try:audit(sample)
        except ValueError:pass
        else:raise AssertionError("malformed conductor accepted")
    # Verify real irreducible one-dimensional character orthogonality
    # on all 30 elements (465 ordered unordered pairs), exactly.
    irr=[[(root(3,(q3*j)%3)*root(5,(q5*k)%5))*
          (-1 if t*q2 else 1) for t,j,k in G]
          for q2,q3,q5 in product(range(2),range(3),range(5))]
    tested=0
    for i,x in enumerate(irr):
        for j,y in enumerate(irr[:i+1]):
            inner=Cyc.scalar(0)
            for u,v in zip(x,y):
                inner=inner+u*v.conjugate()
            assert inner==(30 if i==j else 0)
            tested+=1
    assert tested==465
    return {"status":"PASS","phi_n_conductors":120,
            "group":"C2 x C3 x C5","classes":30,
            "character_orthogonality_pairs":tested,
            "direct_and_dual_Sym2_cases":2,
            "modified_character_counterexample":True,
            "negative_source_input_controls":8,
            "character_rows_are_synthetic_reducible":True,
            "authentic_6Suz_export_checked":False,
            "GAP_or_Agda_executed":False}

if __name__=="__main__":print(json.dumps(run(),indent=2))
