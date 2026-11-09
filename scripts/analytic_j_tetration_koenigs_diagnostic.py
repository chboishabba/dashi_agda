#!/usr/bin/env python3
"""High-precision, NONCERTIFIED local Koenigs diagnostic for exponential.

For the upper fixed point p=-W_{-1}(-1), g(z)=principal_log(z) has
g(p)=p, |g'(p)|=1/|p|<1. The local Schroeder candidate is
chi(z)=lim_{n->infinity} p**n*(g**n(z)-p).

A small floating-point last-jump is NOT a rigorous interval bound,
nor a proof of analytic continuation or Kneser normalization.
"""
import mpmath as mp


def test(dps=80, depth=40):
    mp.mp.dps = dps
    p = -mp.lambertw(-1, -1)
    lam = p
    assert abs(mp.exp(p)-p) < mp.mpf("1e-65")
    assert abs(p) > 1

    def koenigs(z):
        outputs = []
        for n in range(depth):
            outputs.append(lam**n * (z-p))
            z = mp.log(z)
        return outputs[-1], abs(outputs[-1]-outputs[-2])

    for delta in (mp.mpc("0.001", "0"),
                  mp.mpc("0.0001", "0.0002")):
        k, tail = koenigs(p + delta)
        assert tail < mp.mpf("1e-10")
        assert abs(k / delta-1) < mp.mpf("0.001")
        print("point=", mp.nstr(p+delta,20),
              "chi=", mp.nstr(k,20),
              "last-jump=", mp.nstr(tail,6))
    print("upper fixed point:", mp.nstr(p,30))
    print("multiplier absolute value:", mp.nstr(abs(p),20))
    print("PASS: high-precision diagnostics, NOT certified bounds")


if __name__ == "__main__":
    test()
