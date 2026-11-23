#!/usr/bin/env python3
"""MG06 conditional finite KK circle/atomic radial commuting square.
Finite tensor-product analogue only. Coulomb, mass, radius and charge supplied.
"""
from itertools import product
import sympy as s

def radial(n, dr, z, mu, ell):
    b = s.zeros(n + 1, n)
    b[0, 0] = b[n, n - 1] = 1
    for k in range(n - 1):
        b[k + 1, k] = 1
        b[k + 1, k + 1] = -1
    r = [dr * (i + 1) for i in range(n)]
    v = s.diag(*[s.Rational(ell * (ell + 1), 2) / (mu * x*x) - z/x for x in r])
    return b.T * b / (2 * mu * dr*dr) + v

def circle(q):
    b = s.zeros(q, q)
    for j in range(q):
        b[j, j] = 1
        b[j, (j+1) % q] = -1
    return b.T * b

def check():
    cases = 0
    q = 3
    c = circle(q)
    zero = s.ones(q, 1) / s.sqrt(q)
    assert c * zero == s.zeros(q, 1)
    excited = s.Matrix([1, -1, 0]) / s.sqrt(2)
    assert c * excited == 3 * excited
    assert (zero.T * excited)[0] == 0
    for z, ell, mu, radius in product(
        (1, 2), (0, 1), (s.Integer(1), s.Rational(1836, 1837)),
        (s.Integer(1), s.Integer(2))
    ):
        n = 4
        h = radial(n, s.Rational(1, 4), z, mu, ell)
        H = s.kronecker_product(h, s.eye(q)) + s.kronecker_product(s.eye(n), c / radius**2)
        W = s.kronecker_product(s.eye(n), zero)
        assert W.T * W == s.eye(n)
        assert H * W == W * h
        assert W.T * H * W == h
        W1 = s.kronecker_product(s.eye(n), excited)
        assert H * W1 == W1 * (h + 3 / radius**2 * s.eye(n))
        assert H * W1 != W1 * h
        assert H * W != W * radial(n, s.Rational(1, 4), z + 1, mu, ell)
        assert H * W != W * radial(n, s.Rational(1, 4), z, mu + s.Rational(1, 10), ell)
        wrong = h.copy()
        wrong[0, 0] -= 1 / (2 * mu * s.Rational(1, 4)**2)
        assert H * W != W * wrong
        cases += 1
    gs = (s.Integer(1), s.I, -s.Integer(1))
    d = s.diag(*gs)
    c_g = d * c * d.conjugate().T
    W_g = s.kronecker_product(s.eye(4), d * zero)
    h0 = radial(4, s.Rational(1, 4), 1, s.Integer(1), 0)
    H_g = s.kronecker_product(h0, s.eye(q)) + s.kronecker_product(s.eye(4), c_g)
    assert H_g * W_g == W_g * h0
    assert W_g.conjugate().T * W_g == s.eye(4)
    b = s.zeros(q, q)
    for j, u in enumerate((s.I, s.Integer(1), s.Integer(1))):
        b[j, j] = 1
        b[j, (j + 1) % q] = -u
    c_flux = b.conjugate().T * b
    assert c_flux.det() != 0
    assert c_flux * zero != s.zeros(q, 1)
    print(f"PASS {cases}/16 selected-mode commuting squares, isometry, projection and negative controls")
    print("PASS pure-gauge mode transport and nontrivial-holonomy negative control")
    print("OPEN physical KK action, electron mass/charge/spin, 369 map, Coulomb source and continuum")

if __name__ == "__main__":
    check()
