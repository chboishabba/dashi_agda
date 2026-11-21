#!/usr/bin/env python3
"""Exact native P3^3 Laplacian spectral/observer acceptance.
Source: BiologicalFullCubeIncidenceExact.agda (27 sites,54 edges,36 squares).
No physical compactification or electron Hamiltonian is inferred.
"""
from itertools import product
from collections import Counter
import sympy as s

TRITS = (-1, 0, 1)

def native():
    pts = list(product(TRITS, repeat=3))
    edges = [(i,j) for i,a in enumerate(pts) for j,b in enumerate(pts)
             if i < j and sum(abs(x-y) for x,y in zip(a,b)) == 1]
    b = s.zeros(len(edges), 27)
    for row,(i,j) in enumerate(edges):
        b[row,i] = -1
        b[row,j] = 1
    return pts, edges, b.T*b

def path3():
    return s.Matrix([[1,-1,0],[-1,2,-1],[0,-1,1]])

def circle3():
    return s.Matrix([[2,-1,-1],[-1,2,-1],[-1,-1,2]])

def main():
    pts, edges, L = native()
    p, eye = path3(), s.eye(3)
    tensor = (s.kronecker_product(s.kronecker_product(p,eye),eye)
              + s.kronecker_product(s.kronecker_product(eye,p),eye)
              + s.kronecker_product(s.kronecker_product(eye,eye),p))
    assert L == tensor
    assert len(pts) == 27 and len(edges) == 54 and s.trace(L) == 108
    assert p.eigenvals() == {s.Integer(0):1,s.Integer(1):1,s.Integer(3):1}
    expected = Counter(a+b+c for a,b,c in product((0,1,3),repeat=3))
    assert L.eigenvals() == dict(expected)
    assert len(expected) == 9 and sum(expected.values()) == 27
    p9 = s.kronecker_product(p,eye) + s.kronecker_product(eye,p)
    v0 = s.ones(3,1)/s.sqrt(3)
    W = s.kronecker_product(s.eye(9),v0)
    assert W.T*W == s.eye(9)
    assert L*W == W*p9
    assert W.T*L*W == p9
    assert (s.eye(27)-W*W.T)*L*W == s.zeros(27,9)
    raw = []
    for level in TRITS:
        v = s.eye(3)[:,TRITS.index(level)]
        P = s.kronecker_product(s.eye(9),v)
        coupling = (s.eye(27)-P*P.T)*L*P
        assert coupling != s.zeros(27,9)
        raw.append((level,s.trace(coupling.T*coupling)))
    assert raw == [(-1,9),(0,18),(1,9)],raw
    wrong = s.kronecker_product(p9,eye)+s.kronecker_product(s.eye(9),circle3())
    assert wrong != L and s.trace(wrong) == 126
    assert wrong.eigenvals() != L.eigenvals()
    assert circle3().eigenvals() == {s.Integer(0):1,s.Integer(3):2}
    assert s.trace(W.T*L*W) == s.trace(p9) == 24
    assert s.trace(L) == 108
    print('PASS: native 27-site incidence = Cartesian P3^3; 54 edges')
    print('PASS: 27 eigenmodes over',len(expected),'distinct eigenvalues')
    print('PASS: 9-to-27 uniform-mode isometric intertwiner, no leakage')
    print('PASS: sheet leakage quadratic norms',raw)
    print('PASS: C3 periodic-fibre negative control, trace 126 vs 108')
    print('OPEN: physical 5D KK assignment, electron Hamiltonian, units, Agda')

if __name__ == '__main__':
    main()
