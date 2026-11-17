#!/usr/bin/env python3
"""P1(F9) quotient of F81^×: exact 9×8+8=80, chosen split.

Source attribution: original DASHI JFine/Harmonic coarse 9+completion,
PointedTernaryBulk and punctured Kernel4/Kernel2 are set/type producers;
F81 quartic selected in iit_jfine_selected_punctured79_audit.py is a
DASHI-authored choice, not classical modular-j or a Monster action.
"""
from __future__ import annotations
from collections import Counter
from itertools import product
import json
from hashlib import sha256
from iit_jfine_selected_punctured79_audit import (
    ZERO,ONE,POLY,add,multiply,power
)

F81 = tuple(product(range(3),repeat=4))
F9 = tuple(x for x in F81 if power(x,9)==x)
BETA = (0,1,0,0)  # alpha=X mod X^4+X+2, not in F9
INFINITY = ("completionJ",)

def f3scalar(k):
    return (k,0,0,0)

def mul3scalar(k,x):
    return tuple(k*v % 3 for v in x)

def f9coordinates():
    base3={f3scalar(a) for a in range(3)}
    gamma=next(x for x in F9 if x not in base3)
    coords={(a,b):add(f3scalar(a),mul3scalar(b,gamma))
            for a,b in product(range(3),repeat=2)}
    assert len(set(coords.values()))==9 and set(coords.values())==set(F9)
    return coords

def affine_point(x):
    return ("ordinary",x)

def projective_chart():
    assert BETA not in F9 and len(F9)==9
    representations={add(a,multiply(BETA,b)):(a,b)
                     for a,b in product(F9,repeat=2)}
    assert len(representations)==81 and set(representations)==set(F81)
    f9minuszero=tuple(x for x in F9 if x!=ZERO)
    assert len(f9minuszero)==8
    # Each nonzero x decomposes uniquely as an F9 scalar times a
    # selected line representative. The line is P1(F9).
    def to_line_and_scalar(x):
        if x==ZERO: raise ValueError("zero is punctured")
        a,b=representations[x]
        if b==ZERO: return INFINITY,a
        return affine_point(multiply(a,power(b,7))),b
    def from_line_and_scalar(line,scalar):
        if scalar not in f9minuszero: raise ValueError("nonzero F9 scalar required")
        rep=ONE if line==INFINITY else add(line[1],BETA)
        return multiply(scalar,rep)
    outputs={}
    for x in F81:
        if x==ZERO:continue
        point=to_line_and_scalar(x)
        assert from_line_and_scalar(*point)==x
        assert point not in outputs
        outputs[point]=x
    assert len(outputs)==80
    coords=f9coordinates()
    j_markers={("ordinary",pair):affine_point(value)
               for pair,value in coords.items()}
    j_markers[("completionJ",)]=INFINITY
    assert len(j_markers)==10 and len(set(j_markers.values()))==10
    profiles=Counter(line for line,scalar in outputs)
    assert len(profiles)==10 and set(profiles.values())=={8}
    assert profiles[INFINITY]==8
    assert sum(v for k,v in profiles.items() if k!=INFINITY)==72
    assert len(set(tuple(to_line_and_scalar(x) for x in F81 if x!=ZERO)))==80
    return {
       "scope":"exact_finite_projective_trivialisation_noncanonical_section_not_elliptic_j",
       "field":"F81=F3[X]/(X^4+X+2)",
       "subfield":"F9={x:x^9=x}",
       "field_extension_degree_over_F9":2,
       "punctured_F81_count":80,
       "projective_line_F9_points":10,
       "ordinary_affine_points":9,
       "distinguished_completion_point":1,
       "nonzero_vectors_per_line":8,
       "affine_part":72,
       "completion_fibre":8,
       "pointed_coarse_chart_roundtrip":True,
       "nonzero_source_roundtrip":80,
       "chosen_section":True,
       "projective_quotient_canonical_given_F9_subfield":True,
       "infinity_identification_depends_on_chart":True,
       "original_modular_j_identification":False,
       "original_Monster_action_identified":False,
       "source_p2_punctured_action_identified":False,
       "physical_higher_dimension_identified":False,
    }

def audit():
    obj=projective_chart()
    obj["payload_sha256"]=sha256(json.dumps(obj,sort_keys=True).encode()).hexdigest()
    return obj

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
