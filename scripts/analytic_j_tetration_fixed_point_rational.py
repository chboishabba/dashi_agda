#!/usr/bin/env python3
"""Exact rational enclosure of Log(0.318+1.337i) and its Banach disk.

Uses rational artanh-log Taylor bounds, alternating arctan bounds and
Machin's pi identity. All assertions compare fractions, NOT floating point.
The standard transcendental series identities themselves remain analytic
theorem obligations for Agda's Bishop complex owner.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext


def atan_bounds(t, n):
    assert F(0) < t < F(1) and n > 0
    v = sum(((-1)**k) * t**(2*k+1) / F(2*k+1)
            for k in range(n))
    err = t**(2*n+1) / F(2*n+1)
    return (v, v+err) if n % 2 == 0 else (v-err, v)


def half_log_bounds(u, n):
    assert u > 1 and n > 0
    t = (u-1)/(u+1)
    v = sum(t**(2*k+1)/F(2*k+1) for k in range(n))
    err = t**(2*n+1)/(F(2*n+1)*(1-t*t))
    return v, v+err


def maxabs_bounds(bounds):
    return max(abs(bounds[0]), abs(bounds[1]))


def decimal(x):
    with localcontext() as context:
        context.prec = 30
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def verify():
    x = F(318,1000)
    y = F(1337,1000)
    u = x*x + y*y
    assert u == F(1888693,1000000)
    assert F(1374,1000)**2 < u < F(1375,1000)**2

    lnlo, lnhi = half_log_bounds(u,20)
    a5lo, a5hi = atan_bounds(F(1,5),16)
    a239lo, a239hi = atan_bounds(F(1,239),8)
    pi_lo = 16*a5lo - 4*a239hi
    pi_hi = 16*a5hi - 4*a239lo
    assert F(314159265358979,100000000000000) < pi_lo
    assert pi_hi < F(314159265358980,100000000000000)

    atlo, athi = atan_bounds(x/y,18)
    arglo, arghi = pi_lo/2-athi, pi_hi/2-atlo
    dx = maxabs_bounds((lnlo-x,lnhi-x))
    dy = maxabs_bounds((arglo-y,arghi-y))
    assert dx*dx + dy*dy < F(3,10000)**2

    # D(c,0.01): |z|>1.374-0.01 > 4/3 => |Log'(z)|<3/4.
    assert F(1374,1000)-F(1,100) > F(4,3)
    assert F(3,10000) + F(3,4)*F(1,100) < F(1,100)

    # Banach fixed-point p: |p-c|<0.0003/(1-0.75)=0.0012.
    bound = F(3,10000)/(1-F(3,4))
    assert bound == F(12,10000)
    assert F(1374,1000)-bound > F(137,100)
    assert F(1375,1000)+bound < F(138,100)

    # At p, |lambda|=|p|. On D(p,0.1), log inverse
    # derivative <.8 and Koenigs geometric ratio <.8832.
    assert F(1374,1000)-bound-F(1,10) > F(5,4)
    assert (F(1375,1000)+bound)*F(4,5)**2 < F(8832,10000)

    print("PASS: exact rational principal-Log centre inequalities")
    print("centre:", decimal(x), "+", decimal(y), "i")
    print("squared displacement margin:",
          decimal(F(3,10000)**2-dx*dx-dy*dy))
    print("ln absolute bracket:", decimal(lnlo), decimal(lnhi))
    print("argument bracket:", decimal(arglo), decimal(arghi))
    print("Banach r=.01, q=.75, |p-c|<.0012, 1.37<|p|<1.38")
    print("Local Koenigs geometric ratio <.8832")


if __name__ == "__main__":
    verify()
