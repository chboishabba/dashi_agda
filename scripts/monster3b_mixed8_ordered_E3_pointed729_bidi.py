#!/usr/bin/env python3
"""Explicit D4-equivariant E^3 <-> E + (E* x (E + star) x E).

Finite CHOSEN isotypic chart, reuse #1098 AtlasRep D4 source-type and
#1250 mixed-eight result. Not a selected Monster generator or Heisenberg Hom.
"""
import json
from itertools import product
from collections import Counter

E=tuple(product(range(3),repeat=2))
ZERO=(0,0)
Y=tuple(x for x in E if x!=ZERO)
STAR="*"
S=E+(STAR,)


def r(x): return ((-x[1])%3,x[0])
def m(x): return (x[0],(-x[1])%3)


def encode_outer(a,b):
    if a!=ZERO: return (a,b)
    if b!=ZERO: return (b,STAR)
    raise ValueError("central pair has no outer address")


def decode_outer(y,s):
    if y not in Y or s not in S:
        raise ValueError("invalid address")
    return (ZERO,y) if s==STAR else (y,s)


def encode729(a,b,t):
    return ("central",t) if a==ZERO and b==ZERO else (
        "outer",)+encode_outer(a,b)+(t,)


def decode729(p):
    if p[0]=="central": return (ZERO,ZERO,p[1])
    if p[0]=="outer": return decode_outer(p[1],p[2])+(p[3],)
    raise ValueError("unknown pointed label")


def source_action(p,g):
    return tuple(g(x) for x in p)


def target_action(p,g):
    if p[0]=="central": return ("central",g(p[1]))
    y,s,t=p[1:]
    return ("outer",g(y),s if s==STAR else g(s),g(t))


def outer_action(p,g):
    y,s=p
    return (g(y),s if s==STAR else g(s))


def orbit(x,action):
    seen={x};todo=[x]
    while todo:
        p=todo.pop()
        for g in (r,m):
            q=action(p,g)
            if q not in seen:
                seen.add(q);todo.append(q)
    return frozenset(seen)


def orbit_census(points,action):
    remain=set(points)
    result=Counter()
    while remain:
        o=orbit(next(iter(remain)),action)
        assert o<=remain
        result[len(o)]+=1
        remain-=o
    return dict(sorted(result.items()))


def verify():
    x80=[(a,b) for a in E for b in E if a!=ZERO or b!=ZERO]
    labels80=[encode_outer(a,b) for a,b in x80]
    assert len(x80)==80 and len(set(labels80))==80
    assert set(labels80)=={(y,s) for y in Y for s in S}
    for a,b in x80:
        assert decode_outer(*encode_outer(a,b))==(a,b)
        for g in (r,m):
            assert encode_outer(g(a),g(b))==outer_action(encode_outer(a,b),g)
    census80=orbit_census(labels80,outer_action)
    assert census80=={4:8,8:6}

    source=[(a,b,t) for a in E for b in E for t in E]
    addresses=[encode729(*p) for p in source]
    assert len(source)==len(set(addresses))==729
    assert Counter(p[0] for p in addresses)=={"central":9,"outer":720}
    for p in source:
        assert decode729(encode729(*p))==p
        for g in (r,m):
            assert encode729(*source_action(p,g))==target_action(encode729(*p),g)
    census720=orbit_census((p for p in addresses if p[0]=="outer"),target_action)
    assert census720=={4:24,8:78}
    return {
      "schema":"monster3b-mixed8-ordered-E3-pointed729-bidi-v1",
      "source_80_D4_orbit_census":census80,
      "source_720_D4_orbit_census":census720,
      "pointed_729":729,"central_nine":9,"outer_720":720,
      "mixed_target_eight":len(Y),"sheet_ten":len(S),
      "D4_generator_equivariance_incidences":2*(len(x80)+len(source)),
      "ordered_E_splitting_canonically_selected":False,
      "full_Heisenberg_equivariance":False,
      "actual_Monster_intertwiner":False,
      "IIT_causal_interpretation":False,
      "Agda_kernel_verified":False,
      "status":"EXACT_FINITE_CHOSEN_CHART_ONLY"
    }


if __name__=="__main__":
    print(json.dumps(verify(),indent=2,sort_keys=True))
