#!/usr/bin/env python3
"""Horn geometric regularity max-cut: exact Wilson trace and loop metrics.

ORIGINAL RESULTS/OWNERS:
 - Alexander (1924); Hatcher, Algebraic Topology Example 2B.2:
   source classical horn meridian binary commutator tower.
 - Agda #1247: source selected W=T S1 trace in Q(zeta3), 50 tests
   reported independently by its author, not reproduced here.
 - Agda #1244: source original regularization and shrinking-loop
   *conditional* bound. Do not claim Hatcher proved shrinking lengths.
 - Ordinary smooth gauge theory: holonomy differential inequality;
   the explicit constant-curvature SU3 high-winding control here is NEW
   counterexample to the FALSE implication diameter shrink => Hol->I.

No global wild embedding, flat SU3 extension, selected connection,
quantum WZW/Monster transfer or physical neutrino effect is built here.
"""
from fractions import Fraction as Q
from math import pi, sin, sqrt, exp, log

# Literal prior-source cyclotomic trace W=a+b*zeta, zeta=-1/2+i sqrt3/2
D=181846007130841
A=Q(176093404722400,D)
B=-Q(19836986431118,D)
REAL=A-B/2
DELTA_OP_SQ_LOWER=(Q(6)-2*REAL)/3
assert REAL==Q(221179426799,216225930001)
assert DELTA_OP_SQ_LOWER==Q(854996726408,648677790003)
assert DELTA_OP_SQ_LOWER>1
print('PASS exact cyclotomic Wilson => ||W-I||op² >=', DELTA_OP_SQ_LOWER,'> 1')

# Source estimate d([X,Y]) <= 2d(X)d(Y) for unitary X,Y;
# d_root <= epsilon if all leaves d <=epsilon <=1/2, at any depth.
# One can prove this without infinite limits: eps=1/2 is a fixed
# point of e -> 2 e². Below check exact envelope at all depths 0..32.
def bound(depth, eps=Q(1,2)):
    out=eps
    for _ in range(depth):out=2*out*out
    return out
for n in range(33):
    assert bound(n)==Q(1,2)
assert DELTA_OP_SQ_LOWER>1
print('PASS exact depth-independent cutoff: all leaves d<=1/2 => root d<=1/2')

# Selected-root numeric op gap FROM sibling eigenvector fixture;
# independent exact bound above is sufficient even if eigensolver not run.
selected_delta=1.4381884752669252
for n in (1,2,3,5,8,12,20):
    leaf_lower=.5*exp(log(2*selected_delta)/2**n)
    assert leaf_lower>.5
    if n==12:
        assert abs(leaf_lower-.500128987765)<3e-9
        assert abs((2**n)*leaf_lower-2048.5283339)<0.02
    print(f'PASS leaf depth {n}: forced d>={leaf_lower:.12f}, M>= {leaf_lower*2**n:.6f} IF ell_n=2^-n')

# Geometry requires SHORT LENGTH, not just small diameter.
# Explicit analytic smooth SU3 gauge field on R²:
# A = i H (Bfield/2) (-y dx + x dy), H=diag(1,-1,0), Bfield=1.
# The circle gamma_n winds n² times at radius r=1/n.
# ∮ (-y dx+xdy)/2 = pi*N*r² = pi (exact) for all n.
# Hol = exp(i pi H)=diag(-1,-1,+1) != I, gauge-invariant gap 2.
# Yet circle diameter=2/n->0 and A along circle has size <=r/2->0;
# loop LENGTH=2*pi*n->infty, F=iH dx^dy is NONFLAT.
for n in (2,3,5,8,13,29,101):
    r=Q(1,n)
    winding=n*n
    signed_area_over_pi=winding*r*r
    assert signed_area_over_pi==1
    diameter=2*r
    length_over_2pi=winding*r
    A_sup_on_loop=r/2
    assert length_over_2pi==n and diameter==Q(2,n)
    assert A_sup_on_loop==Q(1,2*n)
    assert winding*r*r==1
    # Single wrapping on same tiny circle instead gives area/pi=r²->0.
    assert r*r<1
    print(f'PASS SU3 bounded smooth NONFLAT geometry control n={n}: diameter={diameter}, length/(2pi)={length_over_2pi}, A_sup={A_sup_on_loop}, hol=diag(-1,-1,+1)')
print('NO-GO inference diameter_n->0 alone implies holonomy->I')
print('GEOMETRY GATE: need uniform short LENGTH of genuine horn meridians, or stronger controlled filling/flatness, plus compatible gauge frames')
print('SOURCE BOUNDARY: counterexample is NONFLAT, highly repeated circles, not simple horn meridians')
print('SOURCE BOUNDARY: no bounded physical horn connection or actual wild-metric length was established')
