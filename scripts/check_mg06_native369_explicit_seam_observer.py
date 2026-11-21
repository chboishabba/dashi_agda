#!/usr/bin/env python3
"""MG06: native P3^3 graph versus an explicitly added compact seam.

The source-owned 3x3x3 incidence is nonperiodic. Nine seam edges create
P3^2 x C3; a finite C3 is not a physical five-dimensional KK action.
"""
from collections import Counter
from itertools import product
import sympy as s

TRITS = (-1, 0, 1)

def graph():
    pts = list(product(TRITS, repeat=3))
    edges = [(i, j) for i, x in enumerate(pts) for j, y in enumerate(pts)
             if i < j and sum(abs(a-b) for a,b in zip(x,y)) == 1]
    assert len(edges) == 54
    B = s.zeros(len(edges), 27)
    for k,(i,j) in enumerate(edges):
        B[k,i],B[k,j] = -1,1
    return pts,B.T*B

def seam(pts):
    edges = [(pts.index((x,y,-1)), pts.index((x,y,1)))
             for x,y in product(TRITS,repeat=2)]
    S = s.zeros(9,27)
    for k,(i,j) in enumerate(edges):
        S[k,i],S[k,j] = -1,1
    return S

def main():
    pts,L = graph()
    S = seam(pts)
    delta = S.T*S
    periodic = L+delta
    assert L == L.T and periodic == periodic.T
    assert s.trace(L) == 108 and s.trace(periodic) == 126
    assert delta.rank() == 9 and s.trace(delta) == 18
    assert delta == s.kronecker_product(
        s.eye(9),s.Matrix([[1,0,-1],[0,0,0],[-1,0,1]]))
    assert s.trace(delta*delta) == 36
    p3 = s.Matrix([[1,-1,0],[-1,2,-1],[0,-1,1]])
    c3 = s.Matrix([[2,-1,-1],[-1,2,-1],[-1,-1,2]])
    l9 = s.kronecker_product(p3,s.eye(3))+s.kronecker_product(s.eye(3),p3)
    assert L == s.kronecker_product(l9,s.eye(3))+s.kronecker_product(s.eye(9),p3)
    assert periodic == s.kronecker_product(l9,s.eye(3))+s.kronecker_product(s.eye(9),c3)
    native_spec = Counter(a+b+c for a,b,c in product((0,1,3),repeat=3))
    wrapped_spec = Counter(a+b+c for a,b,c in product((0,1,3),(0,1,3),(0,3,3)))
    assert L.eigenvals() == dict(native_spec)
    assert periodic.eigenvals() == dict(wrapped_spec)
    assert native_spec != wrapped_spec
    W = s.kronecker_product(s.eye(9),s.ones(3,1)/s.sqrt(3))
    assert W.T*W == s.eye(9)
    assert delta*W == s.zeros(27,9)
    assert L*W == W*l9 and periodic*W == W*l9
    for j in range(3):
        Q = s.kronecker_product(s.eye(9),s.eye(3)[:,j])
        assert s.trace(Q.T*delta*Q) == (9 if j != 1 else 0)
    l9_modes = sorted(set(a+b for a,b in product((0,1,3),repeat=2)))
    assert l9_modes == [0,1,2,3,4,6]
    checks = 0
    z = s.Integer(-1)
    for lam in l9_modes:
        rp = ((z-lam)*s.eye(3)-p3).inv()
        rc = ((z-lam)*s.eye(3)-c3).inv()
        u0 = s.ones(3,1)/s.sqrt(3)
        assert (u0.T*rp*u0)[0] == (u0.T*rc*u0)[0] == 1/(z-lam)
        e0 = s.eye(3)[:,0]
        assert (e0.T*rp*e0)[0] != (e0.T*rc*e0)[0]
        assert rc-rp == rc*(c3-p3)*rp
        checks += 1
    assert checks == 6 and S*W == s.zeros(9,9)
    print('PASS native 54 bonds, 9 seam bonds, periodic 63 bonds')
    print('PASS rank-9 seam, trace 108 -> 126, distinct exact spectra')
    print('PASS uniform 9-site observer intertwines both; sheet observer distinguishes')
    print('PASS six exact fibre resolvent comparisons and resolvent identities')
    print('OPEN source-selected physical KK circle, field action, electron and atomic Hamiltonian')

if __name__ == '__main__':
    main()
