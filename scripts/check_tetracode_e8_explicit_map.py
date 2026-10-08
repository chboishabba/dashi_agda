#!/usr/bin/env python3
"""Exact finite/algebraic audit for the tetracode/Eisenstein construction of E8.

DASHI executable evidence only: this script is not an Agda/Lean kernel proof.
It uses only Python integers and exhaustively verifies:

* the tetracode has 9 words, 8 nonzero words of Hamming weight 3;
* the norm-3 Eisenstein Construction-A shell has 240 vectors;
* the shell splits 24 + 216 by zero/nonzero tetracode residue;
* the explicit 8x8 integer matrix M maps those 240 minimal vectors
  bijectively onto the standard doubled-coordinate E8 root set
  (112 integer-family + 128 half-family roots);
* the Eisenstein Gram spectrum is 1,56,126,56,1 after scaling;
* globally, M^T M = 12 G_E, where G_E is four copies of the Eisenstein
  doubled bilinear Gram [[2,-1],[-1,2]].  Thus x=Mv/6 is a scaled isometry
  of the full ambient real quadratic spaces, not merely the root shell.
"""

from collections import Counter
from itertools import product

G1 = (0, 1, 1, 1)
G2 = (1, 0, 1, 2)

M = (
    (0, 0, 0, 0, 3, 0, 3, 0),
    (0, 0, -2, -2, 1, -2, 1, -2),
    (0, 0, -2, 4, 1, -2, 1, -2),
    (0, 0, 4, -2, 1, -2, 1, -2),
    (0, 0, 0, 0, 3, 0, -3, 0),
    (-2, -2, 0, 0, 1, -2, -1, 2),
    (-2, 4, 0, 0, 1, -2, -1, 2),
    (4, -2, 0, 0, 1, -2, -1, 2),
)


def tetracode():
    return {
        tuple((u * G1[i] + v * G2[i]) % 3 for i in range(4))
        for u, v in product(range(3), repeat=2)
    }


def eisenstein_norm(z):
    a, b = z
    return a * a - a * b + b * b


def eisenstein_residue(z):
    a, b = z
    return (a + b) % 3


def eisenstein_bilinear(u, v):
    # 2 Re(sum z_i conj(w_i)) for omega^2 + omega + 1 = 0.
    return sum(
        2 * a * c - a * d - b * c + 2 * b * d
        for (a, b), (c, d) in zip(u, v)
    )


def minimal_tetracode_vectors(code):
    # Norm 3 forces |a|,|b| <= 2, so this finite box is exhaustive.
    vals = tuple(product(range(-2, 3), repeat=2))
    out = []
    for z in product(vals, repeat=4):
        if sum(eisenstein_norm(q) for q in z) != 3:
            continue
        if tuple(eisenstein_residue(q) for q in z) in code:
            out.append(z)
    return out


def standard_doubled_e8_roots():
    roots = set()
    for i in range(8):
        for j in range(i + 1, 8):
            for si, sj in product((-2, 2), repeat=2):
                x = [0] * 8
                x[i], x[j] = si, sj
                roots.add(tuple(x))
    for signs in product((-1, 1), repeat=8):
        if sum(s < 0 for s in signs) % 2 == 0:
            roots.add(tuple(signs))
    return roots


def flatten(z):
    return tuple(q for pair in z for q in pair)


def matvec(matrix, vector):
    return tuple(sum(a * b for a, b in zip(row, vector)) for row in matrix)


def transpose(matrix):
    return tuple(zip(*matrix))


def matmul(left, right):
    rt = transpose(right)
    return tuple(tuple(sum(a * b for a, b in zip(row, col)) for col in rt) for row in left)


def scaled_eisenstein_gram():
    g = [[0] * 8 for _ in range(8)]
    for k in range(4):
        g[2 * k][2 * k] = 24
        g[2 * k][2 * k + 1] = -12
        g[2 * k + 1][2 * k] = -12
        g[2 * k + 1][2 * k + 1] = 24
    return tuple(tuple(row) for row in g)


def explicit_standard_root(z):
    # x = Mv/6 in standard E8 coordinates. Return doubled coordinates 2x=Mv/3.
    mv = matvec(M, flatten(z))
    assert all(q % 3 == 0 for q in mv)
    return tuple(q // 3 for q in mv)


def main():
    code = tetracode()
    assert len(code) == 9
    assert Counter(sum(q != 0 for q in c) for c in code) == Counter({3: 8, 0: 1})

    # Global ambient-space isometry identity.
    assert matmul(transpose(M), M) == scaled_eisenstein_gram()

    shell = minimal_tetracode_vectors(code)
    assert len(shell) == 240
    residue_zero = Counter(
        tuple(eisenstein_residue(q) for q in z) == (0, 0, 0, 0)
        for z in shell
    )
    assert residue_zero == Counter({False: 216, True: 24})

    standard = standard_doubled_e8_roots()
    assert len(standard) == 240
    mapped = [explicit_standard_root(z) for z in shell]
    assert len(set(mapped)) == 240
    assert set(mapped) == standard
    assert all(sum(q * q for q in r) == 8 for r in mapped)

    gram = Counter(eisenstein_bilinear(shell[0], z) for z in shell)
    assert gram == Counter({0: 126, 3: 56, -3: 56, 6: 1, -6: 1})

    print("tetracode words          = 9 = 1 + 8 weight-3")
    print("M^T M identity           = 12 * Eisenstein doubled Gram")
    print("minimal Eisenstein shell = 240 = 24 + 216")
    print("standard E8 roots        = 240 = 112 + 128")
    print("explicit M/6 map         = bijection onto standard E8")
    print("Eisenstein Gram spectrum = {+6:1,+3:56,0:126,-3:56,-6:1}")
    print("RUN_TERMINAL COMPLETE")


if __name__ == "__main__":
    main()
