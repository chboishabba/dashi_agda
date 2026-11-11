#!/usr/bin/env python3
"""Exact generator permutation characters from the 240 = support15 x sign16
B4 carrier. Characters factor under a componentwise action:
fix(g on pairs) = fix(g on supports) * fix(g on signs).
This validates the original Round56 observed 0/56 generator traces
without enumerating an unrelated E8 list or asserting a full F4 action.
"""
from itertools import product

masks=[p for p in product((0,1),repeat=4) if any(p)]
signs=list(product((-1,1),repeat=4))
gs=[("flip",i) for i in range(4)]+[("swap",i) for i in range(3)]

def act_mask(m,g):
    op,i=g
    if op=="flip":return m
    a=list(m);a[i],a[i+1]=a[i+1],a[i]
    return tuple(a)

def act_sign(s,g):
    op,i=g
    a=list(s)
    if op=="flip":a[i]=-a[i]
    else:a[i],a[i+1]=a[i+1],a[i]
    return tuple(a)

def encoded_cell(m,s):
    return tuple((1+v)*x for v,x in zip(m,s))

def test():
    assert len(masks)==15 and len(signs)==16
    whole={(m,s) for m in masks for s in signs}
    assert len(whole)==240
    counts=[]
    for g in gs:
        maskfix=sum(act_mask(m,g)==m for m in masks)
        signfix=sum(act_sign(s,g)==s for s in signs)
        wholefix=sum((act_mask(m,g),act_sign(s,g))==(m,s) for m,s in whole)
        assert wholefix==maskfix*signfix
        counts.append((g,maskfix,signfix,wholefix))
    assert [x[-1] for x in counts]==[0,0,0,0,56,56,56]
    assert all(row[1:]==(15,0,0) for row in counts[:4])
    assert all(row[1:]==(7,8,56) for row in counts[4:])
    assert len({encoded_cell(m,s) for m,s in whole})==240
    print("PASS: B4 character factors pointwise on 15x16 product")
    print("generator; masks fixed, signs fixed, original cells fixed:")
    for row in counts:print(*row)
    print("mod-3 adjacent swap character 56 mod 3 =",56%3)
    print("CONSTRAINT: no full-F4 half16 stability follows")
if __name__=="__main__":test()
