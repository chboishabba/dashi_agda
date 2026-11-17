#!/usr/bin/env python3
"""Exhaustive 27->9->5 native fibre-invariance and honest 729 control.
Existing project owners: #1407 5-in-9/13-in-27; #1414 S3/C3 and
#1244 native balanced ternary end/fibre. Classical orbit quotients.
Neither counts a new wild three-manifold nor proves Monster same-object.
"""
from itertools import product
from collections import defaultdict

T=(-1,0,1)

def orbit(a,b):
    if a==b==0:return 0
    if b==0:return 1
    if a==0:return 2
    if a==b:return 3
    return 4

def audit():
    reps=((0,0),(-1,0),(0,-1),(-1,-1),(-1,1))
    pts=tuple(product(range(3),T,T))
    assert len(pts)==27
    assert tuple(orbit(*p) for p in reps)==tuple(range(5))
    assert all(orbit(a,b)==orbit(-a,-b) for a,b in product(T,repeat=2))
    classes=defaultdict(list)
    for c,a,b in pts:classes[orbit(a,b)].append((c,a,b))
    assert tuple(len(classes[i]) for i in range(5))==(3,6,6,6,6)
    fields=0
    for k in product(range(3),repeat=5):
        f={(c,a,b):k[orbit(a,b)] for c,a,b in pts}
        assert all(f[c,a,b]==f[0,a,b]==f[c,-a,-b] for c,a,b in pts)
        assert tuple(f[0,*rep] for rep in reps)==k
        # An independent sixth C3 phase gives 3 choices, not an
        # additional spatial node or an extra geometric horn.
        for q in range(3):
            assert (tuple(f[0,*rep] for rep in reps),q)==(k,q)
        fields+=1
    assert fields==3**5==243
    assert 3*fields==3**6==729
    # The phase-field group is abelian. A perfect horned source
    # therefore has no nontrivial homomorphism into it.
    print('PASS 27 to 9 to 5 orbit quotient: sizes 3,6,6,6,6')
    print('PASS all 243 invariant fields / 729 independently phased fields')
    print('PASS invariant-field inflate/deflate are pointwise inverse')
    print('BOUNDARY fifth orbit is not a new geometric branching class')
    print('BOUNDARY 729 is optional sixth independent coordinate')
    print('BOUNDARY no wild pi1, SU2 holonomy, RH or Monster same-object')
if __name__=='__main__': audit()
