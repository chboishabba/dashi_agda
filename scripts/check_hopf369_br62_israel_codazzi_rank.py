#!/usr/bin/env python3
"""BR62: exact original 10-row Israel/Codazzi divergence reverse solve.

The signed wall momentum constraint on a physical junction tensor
T_ab is D_q(T)_b = q^a T_ab - q_b tr_eta(T), with eta4=(-+++).
For any NONZERO tangential q, this map Sym²(R^4) -> R^4 is surjective
(rank 4) and has a six-dimensional kernel. This remains true for null
q²=0, where dividing by q² is forbidden. At q=0 the map is rank 0.

A full physical wall must pay D_q(I)_b = 3∂_b j +
[delta Ric(n,e_b)] together with its material variation and connection
terms; free algebraic reverse-solve of four Codazzi components does NOT
prove the nonlinear Einstein–Israel boundary PDE or BR29 propagation.

This checker performs exact rational right inversion, null/timelike/
spacelike and degenerate controls, retention of all 10 Israel entries,
and explicit six-dimensional homogeneous freedom. No numerical rank
thresholds or inverse of the characteristic q².
"""
import argparse
import sympy as s

PAIRS=[(a,b) for a in range(4) for b in range(a,4)]
eta=s.diag(-1,1,1,1)

def sym_components(v):
    T=s.zeros(4)
    for val,(a,b) in zip(v,PAIRS):
        T[a,b]=val
        T[b,a]=val
    return T

def codazzi(q,T):
    qu=eta*q
    trace=s.trace(eta*T)
    return T*qu-q*trace

def pencil(q):
    cols=[]
    for k in range(10):
        v=s.zeros(10,1);v[k]=1
        cols.append(codazzi(q,sym_components(v)))
    return s.Matrix.hstack(*cols)

def rank_source(q,expect):
    A=pencil(q)
    rank=A.rank()
    assert rank==expect,(q,rank,expect)
    if expect==0:
        assert A==s.zeros(4,10)
        print('PASS BR62 zero mode, rank zero, no unsupported inverse')
        return
    kernel=A.nullspace()
    assert len(kernel)==6
    for u in kernel:assert A*u==s.zeros(4,1)
    target=s.Matrix([s.Rational(2*i+3,7) for i in range(4)])
    # Geometric back-solve through original 10 entries. Use rref,
    # choosing four independent columns; do not divide by q².
    _,pivots=A.rref()
    assert len(pivots)==4
    carrier=A[:,list(pivots)]
    x=carrier.inv()*target
    solution=s.zeros(10,1)
    for pivot,value in zip(pivots,x):solution[pivot]=value
    assert A*solution==target
    assert codazzi(q,sym_components(solution))==target
    # Six actual freely variable Israel components are retained; they
    # cannot be thrown away as a scalar constraint closure.
    for k,u in enumerate(kernel):
        added=solution+s.Rational(k+1,13)*u
        assert A*added==target and added!=solution
    assert len(PAIRS)==10
    print('PASS BR62',list(q),'rank',rank,'nullity 6, exact four-source reverse solve')

def run():
    for q in (
        s.Matrix([0,0,0,0]),
        s.Matrix([1,0,0,0]),
        s.Matrix([0,1,0,0]),
        s.Matrix([1,1,0,0]),  # null, q²=0
        s.Matrix([1,s.Rational(3,5),0,0]),
        s.Matrix([0,0,0,1]),
        s.Matrix([1,1,1,0]),
    ):
        qsq=(q.T*eta*q)[0]
        rank_source(q,0 if q==s.zeros(4,1) else 4)
        if q[0]==1 and q[1]==1 and q[2]==0:
            assert qsq==0
    print('BR62 acceptance target: Codazzi rank-all-strata, not nonlinear wall existence')

if __name__=='__main__':run()
