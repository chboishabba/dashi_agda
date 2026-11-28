#!/usr/bin/env python3
"""Certified, rational lower bounds for an original SU(2) Wilson one-link conditional.

On a four-dimensional Wilson lattice an interior positive link is in six
plaquettes. Fix its six three-link staples to +I, respectively -I.
For U in SU(2), t=(1/2)Re Tr U in [-1,1]. Under the normalized SU(2)
Haar law, t=cos(theta), dmu(theta)=(2/pi)sin(theta)^2 dtheta.
The actual conditional Wilson density is proportional to exp(+6 beta t)
or exp(-6 beta t), respectively.

Let A={t>0}. Haar(A)=1/2. Haar({t>=1/2}) =
(1/3-sqrt(3)/(4*pi))>1/6, using sqrt(3)<2 and pi>3.

For beta>=0:
  P_plus(t<=0) <= 3 exp(-3 beta)
  P_minus(t>0) <= 3 exp(-3 beta)
  TV(P_plus,P_minus) >= 1-6 exp(-3 beta)
  L1(P_plus,P_minus) >= 2(1-6 exp(-3 beta))

For integer beta>0, exp(3 beta) >= sum_{k=0}^m (3 beta)^k/k!
gives rigorous exact-rational L1 lower bounds (no float exp).

This excludes a cutoff-independent bare-LINK q<1 L1 Dobrushin
contraction at beta increasing without bound for these admissible
boundary configurations. Does not refute physical CUBE blocking,
continuum YM or any mass gap. Neither SU2 Haar parametrization nor
opposite staple boundary realizability is Agda-kernel certified here.
"""
from fractions import Fraction
from math import factorial


def exp_lower(z: int, order: int) -> Fraction:
    assert z >= 0 and order >= 0
    return sum((Fraction(z**k, factorial(k)) for k in range(order + 1)),
               Fraction(0))


def tv_lower(beta: int, order: int) -> Fraction:
    return 1 - Fraction(6, 1) / exp_lower(3 * beta, order)


def l1_lower(beta: int, order: int) -> Fraction:
    return 2 * tv_lower(beta, order)


def main():
    for beta in (1, 2, 3, 5, 10):
        lo = l1_lower(beta, 4)
        print(f"beta={beta:2d}, 4th-order certified L1 lower bound: "
              f"{lo} = {float(lo):.9f}")
        assert lo <= 2
    assert exp_lower(6, 4) == Fraction(115)
    assert l1_lower(2, 4) == Fraction(218, 115)
    assert l1_lower(2, 4) > 1
    for beta in (1, 2, 3):
        vals = [l1_lower(beta, n) for n in range(10)]
        assert all(a <= b for a, b in zip(vals, vals[1:]))
    print("PASS: exact Fraction SU2 opposite-staple conditional L1 bound")
    print("SCOPE: bare-link, NOT physical R445 cube or continuum YM")


if __name__ == "__main__":
    main()
