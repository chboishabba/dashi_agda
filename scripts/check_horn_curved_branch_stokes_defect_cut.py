#!/usr/bin/env python3
"""Curved-source Hatcher branch acceptance with explicit Wilson homotopy defects.

ORIGINAL MATHEMATICAL SOURCE: Hatcher AT Example 2B.2 group word
m_w=[m_w0,m_w1], but a CURVED connection does not factor through pi1.
Define eta_w = ||Hol_A(gamma_w) -
                  [Hol_A(gamma_w0), Hol_A(gamma_w1)]||op
for genuine BASED source loops. eta depends on a real geometric
homotopy, its transported curvature and a nonabelian-Stokes estimate.
The exact unitary bound d([A,B])<=2 min(d(A),d(B)) then gives
d(root)<=sum_(k=0..n-1) 2^k eta_ancestor(k)+2^n d(leaf).

This is only a source-GATED coefficient compiler, NOT a construction
of curvature, Stokes transport, actual Hatcher loops or neutrino physics.
Flat case eta=0 is the earlier verified one-fast-branch theorem.
"""
from fractions import Fraction as F

def curved_envelope(errors,leaf):
    out=leaf
    for e in reversed(errors):
        assert e>=0
        out=e+2*out
    return out

def explicit_envelope(errors,leaf):
    return sum((F(2)**k*e for k,e in enumerate(errors)),F(0)) + F(2)**len(errors)*leaf

for n in range(21):
    es=[F(1+(k%5),101+7*k) for k in range(n)]
    leaf=F(1,17+n)
    assert curved_envelope(es,leaf)==explicit_envelope(es,leaf)
print("PASS exact arbitrary heterogeneous curvature-defect 0..20 depth recurrence and weighted sum")

# Illustrative marked branch q=1/3, M=100, L0=1.
# If source supplies eta_k <= eps*q^k where eps=1/100 and
# actual loop length <=q^n, then at depth12 the root bound falls BELOW 1.
M,L0,q,eps=F(100),F(1),F(1,3),F(1,100)
n=12
errors=[eps*q**k for k in range(n)]
leaf=M*L0*q**n
bound=curved_envelope(errors,leaf)
assert bound<1
assert F(854996726408,648677790003)>1 # source selected d(W)^2>1.
print('PASS hypothetical NONFLAT rejection n12 q=1/3 M=100 eps=1/100: droot bound=',bound)

# With no geometric/curvature control, eta_root can absorb ANY source W:
# the original pi1 algebra alone is NOT sufficient for a nonflat no-go.
bad=curved_envelope([F(2)]+[F(0)]*11,F(0))
assert bad==2 and bad>1
print('PASS fail-closed nonflat countercontrol: eta_root=2 prevents any rejection')

# At q=1/2, the leaf term never decreases (2q)^n=1;
# no nonflat root no-go follows from an M=100 length cap.
q=F(1,2)
assert all(curved_envelope([F(0)]*n,M*L0*q**n)==M*L0 for n in range(21))
print('PASS critical q=1/2 means no geometric contraction from this bound')

# Product one-branch and curvature sum are algebraic certificates;
# physical eta requires actual surface/homotopy Stokes source data.
print('OPEN source homotopy strip/curvature bound for each Hatcher Z block')
print('OPEN actual marked meridian length/clearance, selected SU3 physical bundle')
