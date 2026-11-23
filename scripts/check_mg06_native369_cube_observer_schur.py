#!/usr/bin/env python3
"""Native 27-voxel/54-bond cube observer Schur regression.
Based on source-owned BiologicalFullCubeIncidenceExact 3x3x3 incidence.
No physical KK/atomic Hamiltonian assertion: H is the graph Laplacian.
"""
from itertools import product
import sympy as S


def native_cube():
    pts = list(product((-1, 0, 1), repeat=3))
    edges = [(i, j) for i, a in enumerate(pts) for j, b in enumerate(pts)
             if i < j and sum(abs(x-y) for x,y in zip(a,b)) == 1]
    assert len(pts) == 27 and len(edges) == 54
    B = S.zeros(len(edges), 27)
    for k, (i, j) in enumerate(edges):
        B[k, i] = -1
        B[k, j] = 1
    return pts, B.T * B


def observe(pts, H, axis, level, z):
    visible = [i for i, p in enumerate(pts) if p[axis] == level]
    hidden = [i for i in range(27) if i not in visible]
    perm = visible + hidden
    G = H.extract(perm, perm)
    A, C, D = G[:9,:9], G[:9,9:], G[9:,9:]
    assert A.shape == (9,9) and D.shape == (18,18)
    ZZ = S.Integer(z)
    residual = C * (ZZ*S.eye(18)-D).inv() * C.T
    reduced = (ZZ*S.eye(9)-A-residual).inv()
    exact = (ZZ*S.eye(27)-G).inv()[:9,:9]
    assert reduced == exact
    assert residual != S.zeros(9,9)
    assert reduced != (ZZ*S.eye(9)-A).inv()
    decoupled = S.diag(A,D)
    assert (ZZ*S.eye(27)-decoupled).inv()[:9,:9] == (ZZ*S.eye(9)-A).inv()
    return S.trace(residual), len([v for v in C if v != 0])


def main():
    pts, H = native_cube()
    assert S.trace(H) == 108 and H*S.ones(27,1) == S.zeros(27,1)
    tests = []
    for axis, level, z in [(0,-1,-1),(0,0,-2),(1,1,-1),(2,0,-2)]:
        tr, links = observe(pts,H,axis,level,z)
        tests.append((axis,level,z,str(tr),links))
    assert tests[0][4] == 9 and tests[1][4] == 18
    for row in tests:
        print("PASS observer axis,level,z,residual trace,boundary links:", *row)
    print("PASS 4/4 exact 27-site source-owned Laplacian Schur squares, nonzero self-energy and uncoupled controls")
    print("OPEN physical KK Hamiltonian, electron source, 369-to-QED map, Agda checker")


if __name__ == "__main__":
    main()
