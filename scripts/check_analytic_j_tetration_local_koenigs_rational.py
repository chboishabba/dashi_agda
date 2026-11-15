#!/usr/bin/env python3
"""Exact rational enclosure for the LOCAL principal-Log Koenigs theorem.

All numerical comparisons below are rational, with explicit arctangent and
logarithm remainder bounds. No floating point used for proof decisions.
This certifies inequalities used in a conventional complex-analysis proof;
it is NOT an Agda/Bishop principal-Log realization or global Kneser theorem.
"""
from fractions import Fraction as Q


def atan_interval(t: Q, count: int = 24) -> tuple[Q, Q]:
    assert 0 < t < 1
    partial = sum(
        ((-1) ** k) * t ** (2 * k + 1) / (2 * k + 1)
        for k in range(count)
    )
    error = t ** (2 * count + 1) / (2 * count + 1)
    return partial - error, partial + error


def log_interval_positive(t: Q, count: int = 24) -> tuple[Q, Q]:
    assert 1 < t
    u = (t - 1) / (t + 1)
    assert 0 < u < 1
    partial = 2 * sum(u ** (2 * k + 1) / (2 * k + 1) for k in range(count))
    error = 2 * u ** (2 * count + 1) / ((2 * count + 1) * (1 - u*u))
    return partial, partial + error


def main() -> None:
    cx, cy = Q(318, 1000), Q(1337, 1000)
    s = cx*cx + cy*cy
    lp0, lp1 = log_interval_positive(s)
    a0, a1 = atan_interval(Q(1, 5))
    b0, b1 = atan_interval(Q(1, 239))
    t0, t1 = atan_interval(cx / cy)
    # Arg(c)=pi/2-atan(cx/cy), pi/2=8atan(1/5)-2atan(1/239)
    residual_re = (lp0/2 - cx, lp1/2 - cx)
    residual_im = (8*a0 - 2*b1 - t1 - cy, 8*a1 - 2*b0 - t0 - cy)
    re_max = max(abs(v) for v in residual_re)
    im_max = max(abs(v) for v in residual_im)
    assert re_max**2 + im_max**2 < Q(3, 10000)**2

    # c lies in the open right half plane, |c|>1.372 and <1.378.
    assert cx > Q(1,100)
    assert s > Q(1372,1000)**2
    assert s < Q(1378,1000)**2

    # Closed disk radius 0.01 centered at c:
    # |Log'(z)| <= 1/(|c|-0.01) < 3/4.
    radius = Q(1, 100)
    assert Q(1372,1000)-radius > Q(4,3)
    assert Q(3,10000) + Q(3,4)*radius < radius
    # Banach: |p-c| <= residual/(1-q) < 0.0012.
    delta = Q(3,10000)/(1-Q(3,4))
    assert delta == Q(12,10000)
    assert Q(1372,1000)-delta > Q(137,100)
    assert Q(1378,1000)+delta < Q(69,50)
    # The principal log is analytic throughout these disks (Re(z)>0).
    assert cx - radius - delta - Q(1,10) > 0

    # On |z-p|<=0.1: |Log'(z)| <= 1/1.27 < 4/5,
    # |Log(p+w)-p-w/p| <= |w|^2/(2*|p|*(|p|-0.1)).
    q = Q(4,5)
    M = Q(311,1000)
    Lambda = Q(69,50)
    beta = Lambda*q*q
    assert Q(1, Q(137,100)-Q(1,10)) < q
    assert Q(1, 2*Q(137,100)*(Q(137,100)-Q(1,10))) < M
    assert beta == Q(552,625) and beta < 1
    constant = Lambda*M/(1-beta)
    assert constant == Q(21459,5840)
    assert constant*Q(1,10) < 1  # chi(z)/(z-p) lies within unit disk of 1.

    print("PASS: rational Machin/arctan/log bounds for |Log(c)-c| < 0.0003")
    print("PASS: certified principal-Log Banach fixed point disk and |p-c|<0.0012")
    print("PASS: 1.37 < |p| < 1.38, branch disk, q=4/5, M=311/1000")
    print("PASS: beta=552/625; Koenigs analytic majorant =21459/5840")
    print("ANALYTIC STEP NOT PROGRAM-CHECKED: Banach, holomorphic Weierstrass theorem,")
    print("derivative/inverse, Schroeder and branch cocycle must be formalized in Bishop.")


if __name__ == "__main__":
    main()
