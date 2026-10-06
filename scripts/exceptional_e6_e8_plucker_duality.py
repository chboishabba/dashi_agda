#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json

P = 3

# E6 quotient bilinear form used by ExceptionalE6Mod3FiniteGeometryExact.
B_E6 = (
    (2, 2, 0, 0, 0),
    (2, 2, 2, 0, 2),
    (0, 2, 2, 2, 0),
    (0, 0, 2, 2, 0),
    (0, 2, 0, 0, 2),
)

# Plucker quadratic q = -p12^2 - p13*p24 + p14*p23.
B_PLUCKER = (
    (2, 0, 0, 0, 0),
    (0, 0, 0, 0, 1),
    (0, 0, 0, 2, 0),
    (0, 0, 2, 0, 0),
    (0, 1, 0, 0, 0),
)

# M^T B_E6 M = 2 B_PLUCKER.
M = (
    (0, 0, 1, 1, 2),
    (0, 0, 0, 0, 1),
    (0, 1, 0, 0, 2),
    (1, 2, 1, 2, 1),
    (1, 0, 2, 1, 2),
)


def matvec(a, v):
    return tuple(sum(a[i][j] * v[j] for j in range(len(v))) % P for i in range(len(a)))


def transpose(a):
    return tuple(tuple(a[j][i] for j in range(len(a))) for i in range(len(a[0])))


def matmul(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(len(b))) % P for j in range(len(b[0])))
        for i in range(len(a))
    )


def bilinear(b, x, y):
    return sum(x[i] * b[i][j] * y[j] for i in range(len(x)) for j in range(len(y))) % P


def rank_mod(a):
    a = [list(row) for row in a]
    m, n = len(a), len(a[0])
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if a[i][c] % P), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = 1 if a[r][c] % P == 1 else 2
        a[r] = [(inv * x) % P for x in a[r]]
        for i in range(m):
            if i != r and a[i][c] % P:
                lam = a[i][c] % P
                a[i] = [(x - lam * y) % P for x, y in zip(a[i], a[r])]
        r += 1
    return r


def canon(v):
    v = tuple(x % P for x in v)
    if not any(v):
        raise ValueError("zero has no projective representative")
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return tuple((inv * x) % P for x in v)
    raise AssertionError("unreachable")


def symplectic4(u, v):
    return (u[0] * v[1] - u[1] * v[0] + u[2] * v[3] - u[3] * v[2]) % P


def pg3_points():
    return sorted({canon(v) for v in itertools.product(range(P), repeat=4) if any(v)})


def symplectic_lines():
    points = pg3_points()
    out = set()
    for a, b in itertools.combinations(points, 2):
        if symplectic4(a, b) != 0:
            continue
        line = set()
        for x, y in itertools.product(range(P), repeat=2):
            v = tuple((x * a[i] + y * b[i]) % P for i in range(4))
            if any(v):
                line.add(canon(v))
        if len(line) == 4:
            out.add(frozenset(line))
    return sorted(out, key=lambda s: sorted(s))


def plucker(line):
    pts = [tuple(x) for x in line]
    u = pts[0]
    v = next(w for w in pts[1:] if canon(w) != canon(u))
    p = (
        u[0] * v[1] - u[1] * v[0],
        u[0] * v[2] - u[2] * v[0],
        u[0] * v[3] - u[3] * v[0],
        u[1] * v[2] - u[2] * v[1],
        u[1] * v[3] - u[3] * v[1],
        u[2] * v[3] - u[3] * v[2],
    )
    p = canon(p)
    assert (p[0] + p[5]) % P == 0
    return p


def plucker5(line):
    p = plucker(line)
    return p[:5]


def e6_image(line):
    return canon(matvec(M, plucker5(line)))


def e6_null_points():
    return sorted({
        canon(v)
        for v in itertools.product(range(P), repeat=5)
        if any(v) and bilinear(B_E6, v, v) == 0
    })


def compute_receipt():
    lhs = matmul(transpose(M), matmul(B_E6, M))
    rhs = tuple(tuple((2 * x) % P for x in row) for row in B_PLUCKER)
    lines = symplectic_lines()
    images = [e6_image(line) for line in lines]
    nulls = e6_null_points()

    pairwise = True
    for i, a in enumerate(lines):
        xa = images[i]
        for j in range(i + 1, len(lines)):
            b = lines[j]
            xb = images[j]
            intersects = bool(a & b)
            orthogonal = bilinear(B_E6, xa, xb) == 0
            if intersects != orthogonal:
                pairwise = False
                break
        if not pairwise:
            break

    return {
        "matrix_rank": rank_mod(M),
        "gram_identity": lhs == rhs,
        "gram_scalar": 2,
        "symplectic_projective_points": len(pg3_points()),
        "symplectic_isotropic_lines": len(lines),
        "e6_null_projective_points": len(nulls),
        "distinct_e6_images": len(set(images)),
        "all_images_null": all(bilinear(B_E6, x, x) == 0 for x in images),
        "image_equals_null_quadric": set(images) == set(nulls),
        "pairwise_incidence_checked": pairwise,
        "line_intersection_iff_e6_orthogonality": pairwise,
        "matrix": M,
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
