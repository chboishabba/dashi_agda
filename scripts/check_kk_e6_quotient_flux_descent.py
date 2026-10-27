#!/usr/bin/env python3
"""Finite diagonal-Z3 quotient flux acceptance test for first-Tits 27.

Attribution: SU(3)^3 trinification / E6 representation root (Slansky 1981);
first-Tits implementation owned by dashi_agda PR #1106; quotient flat
T2 clock/shift witness owned by physical KK PR #1241. This is a NEW
finite Z3 descent audit, not a normalized CS5/APS phase computation.

For lifts of T2 holonomies, central commutator labels (a,b,c) belong
to Z3^3. They commute in G=SU(3)^3/Z3_diag iff a=b=c.
The 27 blocks have center characters a-b,c-a,b-c.
"""
from itertools import product

Z = range(3)
def chars(triple):
    a,b,c=triple
    return ((a-b)%3,(c-a)%3,(b-c)%3)

triples=list(product(Z,repeat=3))
descending=[t for t in triples if chars(t)==(0,0,0)]
assert descending==[(0,0,0),(1,1,1),(2,2,2)]
assert len(descending)==3 and len(triples)==27
# The 27 is faithful for the quotient: any non-diagonal commutator
# fails on at least one source representation block.
assert all(any(chars(t)) for t in triples if t not in descending)
for t in descending:
    assert chars(t)==(0,0,0)
# The two nonzero classes are inaccessible if the three factors are
# incorrectly required to carry individually commuting SU3 lifts.
assert len([t for t in descending if t!=(0,0,0)])==2
# Exactly one quotient flux parameter survives, with 3 distinct values,
# rather than three independent factor flux parameters.
assert len(set(descending))==3
print("PASS center commutator 27/27 exhaustive classification")
print("PASS descent iff diagonal Z3: 0,1,2 flux classes")
print("PASS every non-diagonal flux obstructs the 27 representation")
print("OPEN fractional characteristic classes, full G bundles, CS5 level and APS eta")
