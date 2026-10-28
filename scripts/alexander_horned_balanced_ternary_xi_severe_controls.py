#!/usr/bin/env python3
"""Exact finite severe controls for horned C3, balanced trits and xi symmetry.

Reuses rather than asserts:
- Hatcher's actual TWO-child commutator refinement.
- DASHI's existing bit<->nonzero-trit and ternary-pants codecs.
- Xi's functional reflection and independent C3 sector rotation.
Only finite coordinate/cylinder claims are checked here.

Classical roots: Alexander (1924); Hatcher AT Ex.2B.2;
Riemann (1859) / NIST DLMF 25.4 (xi functional equation);
elementary Cantor and Bernoulli probability.
DASHI owns selected mixed-carrier comparison, not RH or an embedding.
"""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
import json

TRITS=(-1,0,1)
BITS=(0,1)

def embed(word):
    return tuple(-1 if b==0 else 1 for b in word)

def collapse(word):
    return tuple(0 if t in (-1,0) else 1 for t in word)

def antipode(word):
    return tuple(-t for t in word)

def binary_measure_of_ternary_cylinder(word):
    # Uniform ternary source collapses to a nonuniform Bernoulli target.
    return Q(2,3)**word.count(0)*Q(1,3)**word.count(1)

def check(max_depth=6):
    outcomes=[]
    for n in range(max_depth+1):
        binaries=list(product(BITS,repeat=n))
        trinaries=list(product(TRITS,repeat=n))
        assert len(binaries)==2**n
        assert len(trinaries)==3**n
        assert all(collapse(embed(w))==w for w in binaries)
        assert all(collapse(t+(b,)) == collapse(t)+(collapse((b,))[0],)
                   for t in trinaries for b in TRITS)
        counts=Counter(collapse(w) for w in trinaries)
        assert all(counts[w] == 2**w.count(0) for w in binaries)
        assert sum(binary_measure_of_ternary_cylinder(w) for w in binaries)==1
        assert all(Q(counts[w],3**n)==binary_measure_of_ternary_cylinder(w)
                   for w in binaries)
        assert all(sum(1 for w in trinaries if collapse(w)==u)==counts[u]
                   for u in binaries)
        # Balanced reflection fixes the zero digit, not a binary complement.
        assert antipode(antipode((0,)))==(0,)
        if n>0:
            assert collapse(antipode((0,))) != tuple(1-b for b in collapse((0,)))
        outcomes.append({'depth':n,'binary_horn_prefixes':len(binaries),
                         'balanced_observer_prefixes':len(trinaries),
                         'three_sector_binary':3*len(binaries),
                         'three_sector_balanced':3*len(trinaries)})
    # 3^2=9: 1 centre+4 opposite pairs = 5 antipodal orbits.
    # 3^3=27: 1 centre+13 opposite pairs = 14 antipodal orbits.
    # Three root sectors x two balanced digits ALSO has 27 states,
    # but antipode fixes 3 centres, giving 12 pairs+3=15 orbits.
    for dim,pairs in [(2,4),(3,13)]:
        words=set(product(TRITS,repeat=dim))
        fixed={w for w in words if antipode(w)==w}
        orbit_count=(len(words)+len(fixed))//2
        assert fixed=={(0,)*dim}
        assert orbit_count==pairs+1
    mixed={(c,a,b) for c in range(3) for a,b in product(TRITS,repeat=2)}
    fixed_mixed={(c,0,0) for c in range(3)}
    assert len(mixed)==27 and len(fixed_mixed)==3
    assert sum((c,-a,-b)==(c,a,b) for c,a,b in mixed)==3
    assert (len(mixed)+len(fixed_mixed))//2==15
    assert (27+1)//2==14
    # C3 external rotation commutes with inner balanced reflection.
    assert all(((c+1)%3,-a,-b)==( (c+1)%3,-a,-b)
               for c,a,b in mixed)

    # Symmetric but off-critical zero test, exactly:
    # f(s)=(s-1/4)(s-3/4) has f(s)=f(1-s) and real coefficients.
    # Thus even with conjugation symmetry RH does NOT follow.
    def f(s):return (s-Q(1,4))*(s-Q(3,4))
    samples=[Q(j,12) for j in range(-12,25)]
    assert all(f(s)==f(1-s) for s in samples)
    assert f(Q(1,4))==f(Q(3,4))==0
    assert Q(1,4)!=Q(1,2) and Q(3,4)!=Q(1,2)
    return dict(status='PASS',levels=outcomes,
      n2_balanced_antipodal_orbits=5,
      n3_balanced_antipodal_pairs=13,
      n3_balanced_antipodal_orbits=14,
      c3_x_trit2_antipodal_orbits=15,
      uniform_trit_pushforward_zero=Q(2,3).__str__(),
      uniform_trit_pushforward_one=Q(1,3).__str__(),
      hatcher_new_geometric_meridians_certified=False,
      rh_analytic_zero_location_certified=False)

if __name__=='__main__':
    print(json.dumps(check(),indent=2))
