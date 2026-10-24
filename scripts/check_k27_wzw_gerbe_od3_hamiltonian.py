#!/usr/bin/env python3
"""Source-specific SU2 WZW gerbe B-patch transport via O(3,3).

Original prior art: Michael B. Schulz, JHEP06(2012)158,
https://arxiv.org/html/1106.6291v4 , worldsheet Hamiltonian on
TM+T*M and the standard O(d,d) generalized metric/B-transform.
Exact symbolic/rational finite tests; no new physics or BRST proof.
"""
import sympy as s

u,w,z,bn,bs=s.symbols('u w z bN bS', positive=True)
I=s.eye(3); g=s.diag(u,w,z); inv=g.inv()
def B(b): return s.Matrix([[0,0,0],[0,0,b],[0,-b,0]])
north,south=B(bn),B(bs)
delta=north-south
zero=s.zeros(3)
eta=s.BlockMatrix([[zero,I],[I,zero]]).as_explicit()

# Hamiltonian E_B(v,p)=v^T g v+(p+Bv)^T g^-1(p+Bv);
# factor 1/(4pi alpha') common to both sides is omitted.
def generalized_metric(b):
    return s.BlockMatrix([
        [g+b.T*inv*b, b.T*inv],
        [inv*b, inv]
    ]).as_explicit()

# The shift of canonical momentum under north/south patch
# uses p_N=p_S-(B_N-B_S)v for this source convention.
patch=s.BlockMatrix([[I,zero],[-delta,I]]).as_explicit()
assert all(s.simplify(v)==0 for v in patch.T*eta*patch-eta)
assert all(s.simplify(v)==0 for v in
    patch.T*generalized_metric(north)*patch-generalized_metric(south))
print('PASS symbolic O(3,3) B-shift preserves pairing and worldsheet generalized metric')

# Equator chi=theta=pi/2: B_N=+pi r²/2 dtheta^dphi;
# B_S=-pi r²/2 dtheta^dphi, exactly the same sourced gerbe patches.
count=0
for r in [s.Rational(1,3),s.Rational(1),s.Rational(7,2)]:
    bN=s.pi*r*r/2
    bS=-s.pi*r*r/2
    assert s.simplify(bN-bS-s.pi*r*r)==0
    source_g=s.diag(r*r,r*r,r*r)
    for vv in [(1,0,1),(-2,3,4),(1,2,-1)]:
        for pp in [(0,1,0),(2,3,-1),(-1,2,5)]:
            v,p=s.Matrix(vv),s.Matrix(pp)
            pN=p-(B(bN)-B(bS))*v
            def energy(b,mom):
                return ((mom+B(b)*v).T*source_g.inv()*(mom+B(b)*v)
                        +v.T*source_g*v)[0]
            assert s.simplify(energy(bS,p)-energy(bN,pN))==0
            count+=1
assert count==27
print('PASS exact SU2 WZW north/south gerbe patch Hamiltonian:',count,'cases')
print('BOUNDARY B_N-B_S non-exact globally on overlap S2: full gerbe required')
print('BOUNDARY no C3 signed-zero/Monster identification, BRST, full K27/E27 or Clay claim')
