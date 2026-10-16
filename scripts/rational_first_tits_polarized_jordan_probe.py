#!/usr/bin/env python3
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from functools import lru_cache

Q = Fraction
ZERO_M = (Q(0),) * 9
ID_M = (Q(1), Q(0), Q(0), Q(0), Q(1), Q(0), Q(0), Q(0), Q(1))
HALF = Q(1, 2)


def madd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def msub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def mscale(q, a):
    return tuple(q * x for x in a)


def mmul(a, b):
    return tuple(
        sum(a[3 * i + k] * b[3 * k + j] for k in range(3))
        for i in range(3)
        for j in range(3)
    )


def trace(a):
    return a[0] + a[4] + a[8]


def bullet(a, b):
    return mscale(HALF, madd(mmul(a, b), mmul(b, a)))


def bar(a):
    return mscale(HALF, msub(mscale(trace(a), ID_M), a))


def cross(a, b):
    return madd(
        msub(
            msub(bullet(a, b), mscale(HALF * trace(a), b)),
            mscale(HALF * trace(b), a),
        ),
        mscale(HALF * (trace(a) * trace(b) - trace(bullet(a, b))), ID_M),
    )


def jprod(x, y):
    a, b, c = x
    d, e, f = y
    return (
        madd(bullet(a, d), madd(bar(mmul(b, f)), bar(mmul(e, c)))),
        madd(madd(mmul(bar(a), e), mmul(bar(d), b)), cross(c, f)),
        madd(madd(mmul(f, bar(a)), mmul(c, bar(d))), cross(b, e)),
    )


def flatten(x):
    return x[0] + x[1] + x[2]


def basis_element(index: int):
    sector, rc = divmod(index, 9)
    matrix = list(ZERO_M)
    matrix[rc] = Q(1)
    blocks = [ZERO_M, ZERO_M, ZERO_M]
    blocks[sector] = tuple(matrix)
    return tuple(blocks)


BASIS = tuple(basis_element(i) for i in range(27))
BASIS_PRODUCT = tuple(
    tuple(
        {k: value for k, value in enumerate(flatten(jprod(BASIS[i], BASIS[j]))) if value}
        for j in range(27)
    )
    for i in range(27)
)


def add_scaled(out: dict[int, Q], source: dict[int, Q], coefficient: Q) -> None:
    for key, value in source.items():
        new_value = out.get(key, Q(0)) + coefficient * value
        if new_value:
            out[key] = new_value
        else:
            out.pop(key, None)


def sparse_product(v: dict[int, Q], w: dict[int, Q]) -> dict[int, Q]:
    out: dict[int, Q] = {}
    for i, ai in v.items():
        for j, bj in w.items():
            add_scaled(out, BASIS_PRODUCT[i][j], ai * bj)
    return out


def sparse_product_basis(v: dict[int, Q], basis_index: int) -> dict[int, Q]:
    out: dict[int, Q] = {}
    for i, ai in v.items():
        add_scaled(out, BASIS_PRODUCT[i][basis_index], ai)
    return out


TRIPLE = tuple(
    tuple(
        tuple(sparse_product_basis(BASIS_PRODUCT[i][j], k) for k in range(27))
        for j in range(27)
    )
    for i in range(27)
)


def polarized_jordan_basis(a: int, b: int, c: int, y: int) -> dict[int, Q]:
    """Exact fully polarized cubic-in-x Jordan identity on four basis vectors."""
    out: dict[int, Q] = {}
    add_scaled(out, sparse_product_basis(TRIPLE[a][b][y], c), Q(1))
    add_scaled(out, sparse_product_basis(TRIPLE[a][c][y], b), Q(1))
    add_scaled(out, sparse_product_basis(TRIPLE[b][c][y], a), Q(1))
    add_scaled(out, sparse_product(BASIS_PRODUCT[a][b], BASIS_PRODUCT[y][c]), Q(-1))
    add_scaled(out, sparse_product(BASIS_PRODUCT[a][c], BASIS_PRODUCT[y][b]), Q(-1))
    add_scaled(out, sparse_product(BASIS_PRODUCT[b][c], BASIS_PRODUCT[y][a]), Q(-1))
    return out


@lru_cache(maxsize=1)
def verify() -> dict[str, object]:
    support = Counter(len(BASIS_PRODUCT[i][j]) for i in range(27) for j in range(27))
    checked = 0
    first_failure = None
    for a in range(27):
        for b in range(27):
            for c in range(27):
                for y in range(27):
                    residue = polarized_jordan_basis(a, b, c, y)
                    checked += 1
                    if residue:
                        first_failure = (a, b, c, y, residue)
                        return {
                            "basis_product_support": dict(sorted(support.items())),
                            "basis_quadruples_checked": checked,
                            "all_polarized_jordan_quadruples_zero": False,
                            "first_failure": first_failure,
                            "agda_jordan_identity_kernel_proved": False,
                        }
    return {
        "basis_product_support": dict(sorted(support.items())),
        "basis_quadruples_checked": checked,
        "all_polarized_jordan_quadruples_zero": True,
        "first_failure": first_failure,
        "agda_jordan_identity_kernel_proved": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
