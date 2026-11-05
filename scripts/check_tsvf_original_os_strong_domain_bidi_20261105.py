#!/usr/bin/env python3
"""Selected C^2 two-sided original observer/OS analytic control.

The analytic identities mirror the new two-sided real-time TSVF/OS
difference-quotient/domain theorems with one noncollapsed, two-mode,
nontrivial self-adjoint Hamiltonian and a genuine onto unitary J.
This is NOT an instance of a physical Yang-Mills OS reconstruction
or a proof of physical P03/P07; the Agda kernel must be run separately.
"""

import cmath
from fractions import Fraction as F

E0, E1 = F(2, 5), F(13, 7)
HBAR = F(7, 5)
VECS = [
    (complex(1, 2), complex(-1, 3)),
    (complex(0, 1), 0j),
    (0j, complex(3, -1)),
]


def J(v):
    return (v[1], v[0])


def H(v):
    return (complex(E0) * v[0], complex(E1) * v[1])


def HOS(v):
    return J(H(J(v)))


def U(t, v):
    return (
        cmath.exp(-1j * float(E0) * t / float(HBAR)) * v[0],
        cmath.exp(-1j * float(E1) * t / float(HBAR)) * v[1],
    )


def UOS(t, v):
    return J(U(t, J(v)))


def T(tau, v):
    return (
        cmath.exp(-float(E0) * tau / float(HBAR)) * v[0],
        cmath.exp(-float(E1) * tau / float(HBAR)) * v[1],
    )


def TOS(tau, v):
    return J(T(tau, J(v)))


def norm2(v):
    return sum(abs(x) ** 2 for x in v)


def err(a, b):
    return max(abs(x - y) for x, y in zip(a, b))


def main():
    checks = 0
    for v in VECS:
        assert J(J(v)) == v
        assert HOS(J(v)) == J(H(v))
        for t in [-1.1, -0.3, 0.0, 0.2, 2.0]:
            assert err(J(U(t, v)), UOS(t, J(v))) < 1e-12
            assert abs(norm2(U(t, v)) - norm2(v)) < 1e-11
            checks += 2
            for s in [-0.8, 0.0, 0.14]:
                assert err(U(t + s, v), U(t, U(s, v))) < 1e-11
                assert err(UOS(t + s, J(v)), UOS(t, UOS(s, J(v)))) < 1e-11
                checks += 2

        generator = tuple(-1j * z / float(HBAR) for z in H(v))
        previous = 1e10
        for n in range(3, 17):
            dt = 2.0 ** (-n)
            approx = tuple((x - y) / dt for x, y in zip(U(dt, v), v))
            error = err(approx, generator)
            assert error < previous
            previous = error
            assert err(
                J(approx),
                tuple((x - y) / dt for x, y in zip(UOS(dt, J(v)), J(v))),
            ) < 1e-10
            checks += 2
        assert previous < 0.0002

        tau = 0.4
        assert norm2(T(tau, v)) < norm2(v)
        assert err(J(T(tau, v)), TOS(tau, J(v))) < 1e-12
        assert norm2(U(tau, v)) > norm2(T(tau, v))
        checks += 3

    e0, e1 = (1 + 0j, 0j), (0j, 1 + 0j)
    Hprime = lambda v: (complex(E0) * v[0], complex(E1 + 1) * v[1])
    assert H(e0) == Hprime(e0) and H(e1) != Hprime(e1)
    checks += 2
    print(
        f"PASS: {checks} noncollapsed C^2 two-sided real-time/Euclidean, "
        "generator, group and full-domain controls"
    )
    print(
        "REFERENCE ONLY: no physical OS reconstruction, Agda kernel, "
        "or 4D Yang-Mills mass gap"
    )


if __name__ == "__main__":
    main()
