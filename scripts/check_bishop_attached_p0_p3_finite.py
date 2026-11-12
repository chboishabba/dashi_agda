#!/usr/bin/env python3
"""Exact finite arithmetic and negative controls for the attached P0--P3 cut.

PASS is NOT an Agda-kernel proof, Bishop analytic exp/atan, Gamma integral,
eta continuation, zeta irrationality or completed Xi same-object admission.
"""
from fractions import Fraction as F
from math import factorial
from random import Random


def c(a, b=0):
    return F(a), F(b)


def mul(z, w):
    a, b = z
    x, y = w
    return a*x - b*y, a*y + b*x


def conj(z):
    return z[0], -z[1]


def power(z, n):
    out = c(1)
    for _ in range(n):
        out = mul(out, z)
    return out


def plus(z, w):
    return z[0]+w[0], z[1]+w[1]


def minus(z, w):
    return z[0]-w[0], z[1]-w[1]


def check():
    # Original DASHI Cayley: (1+it)/(1-it), not its conjugate.
    p5 = (F(12, 13), F(5, 13))
    p239 = (F(28560, 28561), F(239, 28561))
    qplus = mul(power(p5, 4), conj(p239))
    qminus = mul(power(conj(p5), 4), p239)
    assert qplus == c(0, 1)
    assert qminus == c(0, -1) and qminus == conj(qplus)

    rng = Random(369)
    for _ in range(100):
        terms = [
            c(F(rng.randrange(-50, 51), 17),
              F(rng.randrange(-50, 51), 19))
            for n in range(40)
        ]
        eta = zeta = even = c(0)
        for n in range(21):
            assert plus(eta, plus(even, even)) == zeta
            if n < 20:
                a, b = terms[2*n], terms[2*n + 1]
                eta = plus(eta, minus(a, b))
                zeta = plus(zeta, plus(a, b))
                even = plus(even, b)

    for _ in range(100):
        s = (F(rng.randrange(-25, 26), 11),
             F(rng.randrange(-25, 26), 13))
        reflected = (1-s[0], -s[1])
        assert mul(s, minus(s, c(1))) == (
            mul(reflected, minus(reflected, c(1))))

    # The proposed simple radius/error modulus is FALSE.
    # R=10, eps=1/1000, proposed N=20, but R^20/20! > eps.
    R, n, eps_denominator = 10, 20, 1000
    assert eps_denominator * R**n > factorial(n)

    # Sound but conservative elementary integer-radius bound:
    # N=2R^2+L,  R^N/N!<=2^-L for R>=1, L>=0.
    # At 2R^2, the upper R^2 factorial factors each >=R^2;
    # subsequent factors decrease the ratio by at least 1/2.
    for radius in range(1, 41):
        for log_cutoff in range(31):
            degree = 2*radius*radius + log_cutoff
            assert ((1 << log_cutoff) * radius**degree
                    <= factorial(degree))

    print("PASS 1240 exact conservative factorial cutoff cases")
    print("PASS original positive/opposite Cayley: +i / -i")
    print("PASS 2100 exact original Q[i] finite eta-prefix checks")
    print("PASS 100 exact original Q[i] Xi-polynomial reflection checks")
    print("COUNTEREXAMPLE to attached factorial modulus: "
          f"{F(R**n, factorial(n))} > {F(1, eps_denominator)}")


if __name__ == "__main__":
    check()
