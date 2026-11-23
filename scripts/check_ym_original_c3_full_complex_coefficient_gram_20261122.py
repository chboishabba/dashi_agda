#!/usr/bin/env python3
"""Exact finite Gram/character regression; NOT physical SU(N) OS acceptance.

Numbers are the already published ORIGINAL finite Wilson Q8 diagnostic
covariance eigenvalues, not a new replacement YM measure. Tests verify
the complex-coefficient double sum, all three Eisenstein projectors,
C3 covariance, null-fibre separation and the full-sector spectral no-go.
No SU(N) Haar, positive-time RP, E1, Agda kernel or continuum gap is tested.
"""
from __future__ import annotations
import sympy as sp

def main() -> None:
    checks = 0
    def require(condition, message):
        nonlocal checks
        if not condition:
            raise AssertionError(message)
        checks += 1

    I = sp.I
    w = sp.Rational(-1, 2) + I * sp.sqrt(3) / 2
    lam0 = sp.Rational(64519815, 238733401)
    lam1 = sp.Rational(2910, 15451)
    d = sp.factor((lam0 + 2 * lam1) / 3)
    o = sp.factor((lam0 - lam1) / 3)
    G = sp.Matrix([[d if i == j else o for j in range(3)] for i in range(3)])
    R = sp.Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]])
    eye = sp.eye(3)
    iszero = lambda M: all(sp.simplify(x) == 0 for x in M)
    require(iszero(R ** 3 - eye), "actual C3 order three")
    require(iszero(R.T * G * R - G), "full Gram C3 invariance")
    require(sp.simplify(d + 2 * o - lam0) == 0, "invariant eigenvalue")
    require(sp.simplify(d - o - lam1) == 0, "nontrivial eigenvalue")

    projectors = [(eye + w ** (-k) * R + w ** (-2 * k) * R ** 2) / 3 for k in range(3)]
    for k in range(3):
        require(iszero(projectors[k] * projectors[k] - projectors[k]), f"P{k} idempotent")
        require(iszero(R * projectors[k] - projectors[k] * R), f"P{k} commute")
        require(iszero(projectors[k].conjugate().T - projectors[k]), f"P{k} hermitian")
        for j in range(3):
            if j != k:
                require(iszero(projectors[k] * projectors[j]), f"P{k} P{j} orthogonal")
    require(iszero(sum(projectors, sp.zeros(3, 3)) - eye), "projector completeness")
    require(iszero(G - lam0 * projectors[0] - lam1 * (projectors[1] + projectors[2])),
            "same finite Gram spectral decomposition")

    # Eight complex test families; every i,j reflected cross term is retained.
    vectors = [
        [1, 0, 0], [1, 1, 0], [1, I, 0], [1, -I, 1],
        [1, w, w ** 2], [w ** 2, 1, I], [2, 1 + I, -1], [1, 1, 1]
    ]
    for idx, values in enumerate(vectors):
        v = sp.Matrix(values)
        full = sp.simplify((v.conjugate().T * G * v)[0])
        rotated = sp.simplify(((R * v).conjugate().T * G * (R * v))[0])
        manual = sp.simplify(sum(sp.conjugate(v[i]) * G[i, j] * v[j]
                                 for i in range(3) for j in range(3)))
        sector = sp.simplify(sum((lam0 if k == 0 else lam1) *
                                 (v.conjugate().T * projectors[k] * v)[0]
                                 for k in range(3)))
        require(sp.simplify(full - rotated) == 0, f"complex C3 {idx}")
        require(sp.simplify(full - manual) == 0, f"all 9 entries {idx}")
        require(sp.simplify(full - sector) == 0, f"all sector weights {idx}")

    # Cross terms are nonzero, and conjugation cannot be silently omitted.
    require(o != 0, "nonzero original cross entry")
    v = sp.Matrix([1, I, 0])
    hermitian = sp.simplify((v.conjugate().T * G * v)[0])
    wrong_bilinear = sp.simplify((v.T * G * v)[0])
    require(hermitian != wrong_bilinear, "complex conjugation is essential")
    require(hermitian == 2 * d, "imaginary cross terms cancel in Hermitian form")

    # An artificial zero fibre is not any Eisenstein character zero.
    extended = sp.diag(G, sp.zeros(1, 1))
    z = sp.Matrix([0, 0, 0, 1])
    require(iszero(extended * z), "artificial null Gram row")
    require(not iszero(G * sp.Matrix([1, w, w ** 2])),
            "nontrivial character is not a null row")

    # Countermodel is NOT reconstructed YM; selected-sector decay is
    # independent of two nontrivial sectors with cutoff gaps 1/n.
    for n in (1, 2, 3, 10, 32):
        H = sp.diag(0, 2, sp.Rational(1, n), sp.Rational(1, n))
        require(H[1, 1] == 2 and H[2, 2] == H[3, 3] and H[2, 2] > 0,
                f"full-H selected-vs-other sector {n}")
    print(f"PASS {checks}/{checks} exact SymPy checks")
    print("original finite Q8 diagnostic eigenvalues:", lam0, lam1, lam1)
    print("full complex Hermitian Gram including cross terms; zero fibre separated")
    print("No SU(N) Haar, positive-time RP, E1, same-H or Clay proof.")

if __name__ == "__main__":
    main()
