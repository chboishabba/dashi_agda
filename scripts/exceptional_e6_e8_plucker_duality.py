#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json

P = 3

B_E6 = (
    (2, 2, 0, 0, 0),
    (2, 2, 2, 0, 2),
    (0, 2, 2, 2, 0),
    (0, 0, 2, 2, 0),
    (0, 2, 0, 0, 2),
)

B_PLUCKER = (
    (2, 0, 0, 0, 0),
    (0, 0, 0, 0, 1),
    (0, 0, 0, 2, 0),
    (0, 0, 2, 0, 0),
    (0, 1, 0, 0, 0),
)

M = (
    (0, 0, 1, 1, 2),
    (0, 0, 0, 0, 1),
    (0, 1, 0, 0, 2),
    (1, 2, 1, 2, 1),
    (1, 0, 2, 1, 2),
)

M_INV = (
    (0, 2, 2, 2, 2),
    (0, 1, 1, 0, 0),
    (2, 1, 1, 1, 2),
    (2, 0, 2, 2, 1),
    (0, 1, 0, 0, 0),
)


def add(u, v):
    return tuple((a + b) % P for a, b in zip(u, v))


def smul(a, u):
    return tuple((a * x) % P for x in u)


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
    if not a:
        return 0
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


def span_projective(rows):
    out = set()
    for coeffs in itertools.product(range(P), repeat=len(rows)):
        v = tuple(0 for _ in range(len(rows[0])))
        for c, row in zip(coeffs, rows):
            v = add(v, smul(c, row))
        if any(v):
            out.add(canon(v))
    return frozenset(out)


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
        line = span_projective((a, b))
        if len(line) == 4:
            out.add(line)
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
    return plucker(line)[:5]


def e6_image(line):
    return canon(matvec(M, plucker5(line)))


def e6_null_points():
    return sorted({
        canon(v)
        for v in itertools.product(range(P), repeat=5)
        if any(v) and bilinear(B_E6, v, v) == 0
    })


def line_from_e6_null(x):
    y = matvec(M_INV, x)
    p12, p13, p14, p23, p24 = y
    p34 = (-p12) % P
    skew = (
        (0, p12, p13, p14),
        ((-p12) % P, 0, p23, p24),
        ((-p13) % P, (-p23) % P, 0, p34),
        ((-p14) % P, (-p24) % P, (-p34) % P, 0),
    )
    rows = tuple(row for row in skew if any(row))
    line = span_projective(rows)
    return line, rank_mod(skew)


def compute_receipt():
    lhs = matmul(transpose(M), matmul(B_E6, M))
    rhs = tuple(tuple((2 * x) % P for x in row) for row in B_PLUCKER)
    ident5 = tuple(tuple(1 if i == j else 0 for j in range(5)) for i in range(5))
    lines = symplectic_lines()
    images = [e6_image(line) for line in lines]
    nulls = e6_null_points()

    pairwise = True
    for i, a in enumerate(lines):
        xa = images[i]
        for j in range(i + 1, len(lines)):
            b = lines[j]
            xb = images[j]
            if bool(a & b) != (bilinear(B_E6, xa, xb) == 0):
                pairwise = False
                break
        if not pairwise:
            break

    inverse_ok = True
    inverse_rank_two = True
    inverse_isotropic = True
    for x in nulls:
        line, rank = line_from_e6_null(x)
        inverse_rank_two &= rank == 2
        inverse_isotropic &= len(line) == 4 and all(
            symplectic4(a, b) == 0 for a, b in itertools.combinations(line, 2)
        )
        inverse_ok &= e6_image(line) == x

    return {
        "matrix_rank": rank_mod(M),
        "inverse_matrix_identity": matmul(M, M_INV) == ident5 and matmul(M_INV, M) == ident5,
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
        "inverse_skew_rank_two_all40": inverse_rank_two,
        "inverse_planes_symplectic_isotropic_all40": inverse_isotropic,
        "two_sided_roundtrip_all40": inverse_ok,
        "matrix": M,
        "inverse_matrix": M_INV,
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
