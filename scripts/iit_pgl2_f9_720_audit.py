#!/usr/bin/env python3
"""Finite PGL2(F9) action and Singer C10/C5 bridge, source-aware, not physics.

Relates the *new* projective action to the literal 9+infinity point carrier,
not to the source D4 square action or classical modular-j transformation law.
"""
from __future__ import annotations
from itertools import product
import json
from hashlib import sha256
from iit_jfine_selected_punctured79_audit import (
    ZERO, ONE, add, multiply, power
)
from iit_projective_f9_pointed80_audit import F81,F9,BETA


def audit():
    zero,one=ZERO,ONE
    pairs={add(a,multiply(BETA,b)):(a,b) for a,b in product(F9,repeat=2)}
    assert len(pairs)==81
    def project(x):
        a,b=pairs[x]
        return ("infinity",) if b==zero else ("affine",multiply(a,power(b,7)))
    points=[("infinity",)]+[("affine",x) for x in F9]
    ids={pt:i for i,pt in enumerate(points)}
    assert len(ids)==10
    perms=set()
    for a,b,c,d in product(F9,repeat=4):
        determinant=add(multiply(a,d),multiply((2,0,0,0),multiply(b,c)))
        if determinant==zero:continue
        outputs=[]
        for pt in points:
            x,y=(one,zero) if pt[0]=="infinity" else (pt[1],one)
            X=add(multiply(a,x),multiply(b,y))
            Y=add(multiply(c,x),multiply(d,y))
            image=("infinity",) if Y==zero else ("affine",multiply(X,power(Y,7)))
            outputs.append(ids[image])
        perms.add(tuple(outputs))
    assert len(perms)==720
    stabilizer={p for p in perms if p[0]==0}
    assert len(stabilizer)==72
    generator=next(x for x in F81 if x!=zero and
                   power(x,40)!=one and power(x,16)!=one and
                   power(x,80)==one and power(x,8)!=one)
    def mulperm(g):
        return tuple(ids[project(multiply(
            g, one if point[0]=="infinity" else add(point[1],BETA)
        ))] for point in points)
    ten=mulperm(generator)
    assert power(generator,80)==one
    assert all(power(generator,80//prime)!=one for prime in (2,5))
    assert ten in perms
    five=tuple(ten[ten[i]] for i in range(10))
    def cycles(p):
        seen=set(); result=[]
        for i in range(10):
            if i in seen:continue
            cyc=[];j=i
            while j not in seen:
                seen.add(j);cyc.append(j);j=p[j]
            result.append(cyc)
        return result
    assert sorted(len(c) for c in cycles(ten))==[10]
    assert sorted(len(c) for c in cycles(five))==[5,5]
    assert ten[0]!=0 and five[0]!=0
    receipt={
        "source":"PGL2(F9) from F81 chosen field chart",
        "group_order":720,
        "affine_infinity_stabilizer_order":72,
        "point_count":10,
        "homogeneous_space_index":10,
        "Singer_order10_cycle_lengths":[10],
        "Singer_order5_cycle_lengths":[5,5],
        "order5_moves_completion_infinity":True,
        "C5_in_affine_stabilizer":False,
        "identified_with_original_D4_sheet_action":False,
        "identified_with_classical_modular_j_action":False,
        "status":"finite arithmetic; no Agda PGL2 group kernel receipt"
    }
    receipt["payload_sha256"]=sha256(json.dumps(receipt,sort_keys=True).encode()).hexdigest()
    return receipt


if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
