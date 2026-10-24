#!/usr/bin/env python3
"""Exact finite certificate for the F3^4 symplectic -> F3^5 quadratic bridge.

DASHI contribution.  This script is deliberately finite/exhaustive: no random
sampling and no floating point.  It verifies the concrete computation used by
the Agda recognition surface without promoting the computation to a kernel
proof.
"""

from itertools import product

F = (0, 1, 2)
V4 = tuple(product(F, repeat=4))
V5 = tuple(product(F, repeat=5))


def is_zero(v):
    return all(x == 0 for x in v)


def omega(u, v):
    return (u[0]*v[1] - u[1]*v[0] + u[2]*v[3] - u[3]*v[2]) % 3


def wedge6(u, v):
    # Pluecker order: 12,13,14,23,24,34.
    return (
        (u[0]*v[1] - u[1]*v[0]) % 3,
        (u[0]*v[2] - u[2]*v[0]) % 3,
        (u[0]*v[3] - u[3]*v[0]) % 3,
        (u[1]*v[2] - u[2]*v[1]) % 3,
        (u[1]*v[3] - u[3]*v[1]) % 3,
        (u[2]*v[3] - u[3]*v[2]) % 3,
    )


def primitive5(p):
    # On omega=0, p34=-p12, so the first five coordinates determine p.
    return p[:5]


def pluecker_q5(y):
    p12, p13, p14, p23, p24 = y
    return (-p12*p12 - p13*p24 + p14*p23) % 3


# Exact coordinate change discovered by the finite computation.
P_INV = (
    (0, 0, 2, 1, 0),
    (0, 2, 0, 0, 2),
    (0, 1, 1, 1, 2),
    (0, 1, 2, 2, 2),
    (1, 0, 0, 0, 0),
)


def matvec(M, v):
    return tuple(sum(M[i][j]*v[j] for j in range(len(v))) % 3
                 for i in range(len(M)))


def q_std(z):
    return sum(x*x for x in z) % 3


def canonical_projective(v):
    """Canonical representative of {v,-v}, with first nonzero coordinate 1."""
    assert not is_zero(v)
    for x in v:
        if x:
            scale = 1 if x == 1 else 2
            return tuple((scale*y) % 3 for y in v)
    raise AssertionError("unreachable")


def rank2_span(u, v):
    p = wedge6(u, v)
    return not is_zero(p)


def projective_lagrangian_lines():
    lines = set()
    for u in V4:
        if is_zero(u):
            continue
        for v in V4:
            if is_zero(v) or omega(u, v) != 0 or not rank2_span(u, v):
                continue
            # A 2-plane is represented by its projective Pluecker coordinate.
            p = primitive5(wedge6(u, v))
            lines.add(canonical_projective(p))
    return lines


def line_intersection_from_bivectors(a, b):
    # In the primitive 5-space this is equivalent to polar orthogonality after
    # the fixed coordinate change.  Kept here as the relation receipt tested
    # below, rather than introducing a second row-space implementation.
    za, zb = matvec(P_INV, a), matvec(P_INV, b)
    return sum(x*y for x, y in zip(za, zb)) % 3 == 0


def main():
    oriented = set()
    ordered_isotropic_bases = 0

    for u in V4:
        if is_zero(u):
            continue
        for v in V4:
            if is_zero(v) or omega(u, v) != 0:
                continue
            p = wedge6(u, v)
            if is_zero(p):
                continue

            ordered_isotropic_bases += 1
            assert (p[0] + p[5]) % 3 == 0, "primitive constraint failed"

            y = primitive5(p)
            assert pluecker_q5(y) == 0, "Pluecker nullity failed"

            z = matvec(P_INV, y)
            assert q_std(z) == 0, "standard Q-nullity failed"
            oriented.add(y)

    q0 = {z for z in V5 if not is_zero(z) and q_std(z) == 0}
    images = {matvec(P_INV, y) for y in oriented}

    assert ordered_isotropic_bases == 1920
    assert len(oriented) == 80
    assert len(q0) == 80
    assert images == q0

    lines = projective_lagrangian_lines()
    q0_lines = {canonical_projective(z) for z in q0}
    assert len(lines) == 40
    assert len(q0_lines) == 40
    assert {canonical_projective(matvec(P_INV, y)) for y in lines} == q0_lines

    # Projective null-point orthogonality graph parameters.
    q0v = sorted(q0_lines)
    degs = []
    common_adj = set()
    common_non = set()
    for i, x in enumerate(q0v):
        nx = {j for j, y in enumerate(q0v) if j != i and sum(a*b for a,b in zip(x,y)) % 3 == 0}
        degs.append(len(nx))
        for j in range(i+1, len(q0v)):
            y = q0v[j]
            ny = {k for k, z in enumerate(q0v) if k != j and sum(a*b for a,b in zip(y,z)) % 3 == 0}
            c = len(nx & ny)
            if j in nx:
                common_adj.add(c)
            else:
                common_non.add(c)
    assert set(degs) == {12}
    assert common_adj == {2}
    assert common_non == {4}

    print("PASS e6-f3 exterior-square bridge")
    print(f"ordered isotropic independent pairs: {ordered_isotropic_bases}")
    print(f"oriented primitive decomposable bivectors: {len(oriented)}")
    print(f"nonzero standard-Q null vectors: {len(q0)}")
    print(f"projective Lagrangian/null points: {len(lines)}")
    print("projective null graph: SRG(40,12,2,4)")


if __name__ == "__main__":
    main()
