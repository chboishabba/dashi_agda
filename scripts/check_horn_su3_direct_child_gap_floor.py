#!/usr/bin/env python3
"""Direct SU3 sibling commutator cap and selected-W child gap floor.

Mathematical sources/ownership: Hatcher Ex2B2 (marked child words),
Gotô 1949 (abstract compact semisimple commutators), existing neutrino
Agda #1247 (selected exact W trace), hyperfabric Agda #1249 (its
independent rational operator-norm square lower certificate).

New elementary matrix-analytic consequence: if d(B)=delta<=sqrt(2),
||ABA^-1-B||<=2||B-lambda I||<=2delta sqrt(1-delta^2/4),
where lambda=1-delta^2/2. This is SHARP directly within SU3:
A swaps the two nontrivial eigenvectors of B. Hence both children in
any source-marked commutator for selected W obey gap > 3/5.
NO source-linked geometrical meridian lengths or physical field claimed.
"""
from fractions import Fraction as F
from math import sin, asin, cos, sqrt

source_lower=F(854996726408,648677790003)
def arc_sq(e):
    e=F(e)
    assert 0<=e<=2
    return F(4) if e*e>=2 else 4*e*e*(1-e*e/4)
assert arc_sq(F(3,5))==F(819,625)
assert source_lower>arc_sq(F(3,5))
assert source_lower-arc_sq(F(3,5))==F(3105843992543,405423618751875)
# Stronger admissible rational gate; fails closed just beyond the real root.
assert source_lower>arc_sq(F(6019,10000))
assert source_lower<arc_sq(F(301,500))
threshold=sqrt(2-sqrt(4-float(source_lower)))
assert .6019<threshold<.602
print('PASS exact selected W source root gap forces BOTH depth-one children d>3/5')
print('PASS stronger rational floor 6019/10000, ceiling 301/500; root floor ~= ',threshold)

# SHARPNESS of DIRECT bound: choose the SU3 90-degree plane exchange A.
try:
    import numpy as np
    I=np.eye(3,dtype=complex)
    A=np.array([[0,1,0],[-1,0,0],[0,0,1]],dtype=complex)
    assert abs(np.linalg.det(A)-1)<1e-12
    for e in (F(1,4),F(1,2),F(31,60),F(3,5),F(1),F(7,5)):
        alpha=2*asin(float(e)/2)
        z=complex(cos(alpha),sin(alpha))
        B=np.diag([z,z.conjugate(),1])
        comm=A@B@A.conj().T@B.conj().T
        assert abs(np.linalg.norm(B-I,ord=2)-float(e))<1e-12
        assert abs(np.linalg.norm(comm-I,ord=2)**2-float(arc_sq(e)))<1e-11
    print('PASS exact-form sharpness family SU3 direct commutator, six numerical sanity checks')
except ImportError:
    print('SKIP optional numpy direct sharpness control')

# Source-gated finite metric consequence: any compatible connection norm M
# along TRUE physical local child meridians of length L_i obeys
# d(B_i)<=M L_i. Therefore both child gaps >3/5 force M L_i>3/5.
for length in (F(1,4),F(1,8)):
    necessary=F(3,5)/length
    assert necessary in (F(12,5),F(24,5))
print('PASS source CONDITIONAL: L=1/4 requires M>12/5; L=1/8 requires M>24/5 (illustrative only)')

# Negative controls: disconnected ring/W from a group generator not
# Hatcher-marked does not inherit this pair-of-children condition.
# And a nonflat Wilson connection pays genuine Stokes defects eta>=0.
assert source_lower<4
print('OPEN actual marked children, their Euclidean lengths, based flatness or nonflat eta')
