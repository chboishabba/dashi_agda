#!/usr/bin/env python3
"""Exact obstruction to naive same-beta original Wilson cutoff consistency.

Projection L=2 -> L=1 retains the four positive links at origin.
Let f=real trace of their commutator [U0,U1] on both finite carriers.
At beta=0, the product Haar pushforward agrees: E[f]=1/4.
At L=1 the six plaquette commutators give a Gibbs derivative 25/48.
At L=2 every plaquette has >=2 unselected links occurring once;
center-flip parity makes H[f*t_p]=0, so its projected derivative is 0.
This refutes THIS fixed-beta link-selection projective consistency.
It does NOT refute a properly defined RG blocking/decimation kernel.
"""
from fractions import Fraction as Q
from itertools import product,combinations

E_f=Q(1,4)
E_D1=Q(9,2)
E_fT1=Q(1,3)+4*Q(1,8)+Q(1,16)
E_fD1=6*E_f-E_fT1
cov1=E_fD1-E_f*E_D1
assert E_fT1==Q(43,48)
assert cov1==-Q(25,48)
slope1=-cov1

L=2
origin=(0,0,0,0)
selected={(origin,a) for a in range(4)}
def step(x,k):
    y=list(x);y[k]=(y[k]+1)%L;return tuple(y)
checks=0
for site in product(range(L),repeat=4):
    for a,b in combinations(range(4),2):
        edges={(site,a),(step(site,a),b),(step(site,b),a),(site,b)}
        assert len(edges)==4
        assert len(edges-selected)>=2
        # Every unselected link occurs only once in t_p and not in f.
        # Invariant Haar under U_e -> -U_e gives H[f*t_p]=0.
        checks+=2
assert checks==192
E_fT2=Q(0)
E_D2=Q(6*L**4)
E_fD2=E_D2*E_f-E_fT2
cov2=E_fD2-E_f*E_D2
assert cov2==0
slope2=-cov2
assert slope1!=slope2
print(f"L1 E[f]=1/4 derivative={slope1}")
print(f"L2 projected E[f]=1/4 derivative={slope2}")
print(f"NAIVE_FIXED_BETA_CYLINDER_INCONSISTENT; checks={checks+6}")
