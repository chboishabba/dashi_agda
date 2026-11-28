#!/usr/bin/env python3
"""Exact finite Q8 check of R445 weighted block pushforward algebra.

Q8 is only a noncommuting finite subgroup of SU(2), NOT continuous compact
SU(N) Haar or the selected four-dimensional Wilson Gibbs measure.

The 2-link closed-path block B(a,b)=ab has a gauge-invariant positive toy
fine density w(a,b)=2+Re(ab). Its ACTUAL pushforward mass is computed
through the original fine pairs, not declared to be bare coarse Haar.
Demonstrates normalization, numerator linearity/positivity, source gauge
invariance, and a counterexample to automatic *bare Wilson* closure.
The exact Agda owner uses the actual original #1444 physical SU(N) source
conditionally on one-link Haar: the Q8 harness checks only conventions.
"""
from fractions import Fraction as Q
from itertools import product

E = (1, 0, 0, 0)
I = (0, 1, 0, 0)
J = (0, 0, 1, 0)
K = (0, 0, 0, 1)
Q8 = [E, (-1, 0, 0, 0), I, (0, -1, 0, 0),
      J, (0, 0, -1, 0), K, (0, 0, 0, -1)]


def mul(a, b):
    w, x, y, z = a
    v, p, q, r = b
    return (w*v-x*p-y*q-z*r, w*p+x*v+y*r-z*q,
            w*q-x*r+y*v+z*p, w*r+x*q-y*p+z*v)


def inv(a):
    return a[0], -a[1], -a[2], -a[3]


def block(a, b):
    return mul(a, b)


def weight(a, b):
    value = 2 + block(a, b)[0]
    assert value >= 1
    return Q(value)


def numerator(f):
    return sum((weight(a, b) * f(block(a, b))
                for a, b in product(Q8, repeat=2)), Q(0))


def run():
    # The actual fine weight is counted before projecting.
    total = numerator(lambda g: Q(1))
    assert total == 128
    coarse_mass = {
        g: sum((weight(a, b)
                for a, b in product(Q8, repeat=2)
                if block(a, b) == g), Q(0))
        for g in Q8
    }
    assert sum(coarse_mass.values()) == total
    assert all(coarse_mass[g] == 8 * (2 + g[0]) for g in Q8)

    f = lambda g: Q(g[0])
    h = lambda g: Q(1 if g == E else 0)
    assert numerator(lambda g: f(g) + h(g)) == numerator(f) + numerator(h)
    for scale in (Q(-2), Q(0), Q(2, 3)):
        assert numerator(lambda g: scale * f(g)) == scale * numerator(f)
    assert numerator(lambda g: Q(0)) == 0
    assert numerator(lambda g: Q(g[0] * g[0])) >= 0

    # Uniform source gauge rotations at an intermediate site cancel;
    # closed start/end gauge is conjugation, preserving Re SU2 trace.
    checks = 0
    for a, b, g0, gm in product(Q8, repeat=4):
        aa = mul(mul(g0, a), inv(gm))
        bb = mul(mul(gm, b), inv(g0))
        assert block(aa, bb) == mul(mul(g0, block(a, b)), inv(g0))
        assert weight(aa, bb) == weight(a, b)
        checks += 1

    # Actual pushforward P(identity)=3/16, bare-uniform P=1/8.
    actual = coarse_mass[E] / total
    assert actual == Q(3, 16)
    assert actual != Q(1, 8)

    # Stronger: w(g)=2+Re(g) cannot be proportional to ANY bare
    # exp(beta Re(g)) density on Q8, since such a density must obey
    # w(+1)*w(-1)=w(0)^2. Here 3*1 != 2*2, exactly.
    assert (2 + E[0]) * (2 + (-1)) != (2 + I[0])**2

    print(f"PASS {checks} exact Q8 source gauge-cancellation checks; "
          f"{len(Q8)**2} full fine-pair weighted masses; "
          "pushforward positivity/linearity/normalization and "
          "non-bare cross-ratio negative control")
    print("REFERENCE ONLY: not physical 4D SU(N) Haar, RG, OS or mass gap")


if __name__ == "__main__":
    run()
