#!/usr/bin/env python3
"""Exact 16-element linear-flag subfamily of #1250 MIXED8 charts.

For each nonzero D4-linear q:E+E->E (8 such coefficient pairs), choose
one of the two D4-linear isomorphisms ker(q)->E. Use q outside ker(q)
and the chosen isomorphism on its nonzero kernel. This yields ten
preimages of each target point, with an explicit D4-action.
CLASSICAL finite module computation on a CHOSEN E+E source chart.
NOT an actual selected Monster equivariant or IIT operator.
"""
import json
from itertools import product
from collections import Counter

import monster3b_mixed8_ordered_E3_pointed729_bidi as codec

E=codec.E
ZERO=codec.ZERO
F=range(3)
X=tuple((x,y) for x in E for y in E if x!=ZERO or y!=ZERO)


def scalar(a,x):return ((a*x[0])%3,(a*x[1])%3)
def add(x,y):return ((x[0]+y[0])%3,(x[1]+y[1])%3)


def kernel_generator(a,b):
    return next((c,d) for c,d in product(F,repeat=2)
                if (c,d)!=(0,0) and (a*c+b*d)%3==0)


def flag_map(a,b,sign):
    """Return complete source80->target8 function as 80-tuple of values."""
    assert (a,b)!=(0,0) and sign in (1,2)
    c,d=kernel_generator(a,b)
    out=[]
    for x,y in X:
        z=add(scalar(a,x),scalar(b,y))
        if z!=ZERO:
            out.append(z)
            continue
        u=scalar(pow(c,-1,3),x) if c else scalar(pow(d,-1,3),y)
        assert scalar(c,u)==x and scalar(d,u)==y and u!=ZERO
        out.append(scalar(sign,u))
    return tuple(out)


def source_linear_action(matrix,p):
    a,b,c,d=matrix
    x,y=p
    return add(scalar(a,x),scalar(b,y)),add(scalar(c,x),scalar(d,y))


def verify():
    candidate={}
    index={p:i for i,p in enumerate(X)}
    for a,b in product(F,repeat=2):
        if (a,b)==(0,0):
            continue
        for sign in (1,2):
            f=flag_map(a,b,sign)
            assert Counter(f)=={y:10 for y in codec.Y}
            for x,y in X:
                for g in (codec.r,codec.m):
                    assert f[index[(g(x),g(y))]]==g(f[index[(x,y)]])
            candidate[(a,b,sign)]=f
    assert len(candidate)==len(set(candidate.values()))==16
    fam=set(candidate.values())
    matrices=[(a,b,c,d) for a,b,c,d in product(F,repeat=4)
              if (a*d-b*c)%3]
    assert len(matrices)==48
    stabilizers=Counter()
    for f in fam:
        fixed=0
        for matrix in matrices:
            transported=tuple(f[index[source_linear_action(matrix,p)]]
                              for p in X)
            assert transported in fam
            fixed+=transported==f
        stabilizers[fixed]+=1
    assert stabilizers=={3:16}
    return {
      "schema":"monster3b-mixed8-linear-flag-family-v1",
      "linear_D4_surjections_E2_to_E":8,
      "kernel_D4_isomorphisms_per_surjection":2,
      "distinct_D4_equivariant_balanced_maps":16,
      "preimages_per_target_label":10,
      "source_D4_centralizer_order":48,
      "source_centralizer_orbits_on_flag_family":1,
      "source_centralizer_stabilizer_order":3,
      "all_20m_charts_selected":False,
      "canonical_full_source_invariant_chart":False,
      "actual_Monster_normalizer_verified":False,
      "Agda_kernel_verified":False,
      "status":"EXACT_FINITE_FLAG_CHART_ONLY"
    }


if __name__=="__main__":
    print(json.dumps(verify(),indent=2,sort_keys=True))
