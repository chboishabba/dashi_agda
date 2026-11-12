#!/usr/bin/env python3
"""Exact-rational enclosure: refute a sigma-only complex eta tail bound.

At s=2+20i, N=4, the asserted
  |eta(s)-sum_{n<=N}(-1)^(n-1)n^(-s)| <= 2/(N+1)^Re(s)
is FALSE. Certify the finite tail n=5..100 via Q[i] enclosures;
bound the remaining infinite tail absolutely by 1/100.

Elementary analytic lemmas behind these rational comparisons:
  ln x = 2 sum_{j>=0}u^(2j+1)/(2j+1), u=(x-1)/(x+1)
  atan x alternating with next-term error (0<x<1)
  pi = 16 atan(1/5)-4 atan(1/239)
  |e^(ia)-e^(ib)| <= |a-b|, a,b real
  |e^(ia)-sum_{k=0}^40 (ia)^k/k!| <= 100*4^41/41!, |a|<=4
  sum_{n=101}^infinity n^-2 <= integral_100^infinity x^-2 dx = 1/100

No mpmath, float-rounding trust, native Bishop proof, Agda kernel
receipt, or claim of completed analytic continuation. The float
rounding selects an integer period; all bounds validate that choice.
"""
from fractions import Fraction as Q
from math import factorial, log, pi


def log_atanh_interval(x, terms=28):
    assert 1 <= x <= 2
    u = (x-1)/(x+1)
    lower = sum((2*u**(2*j+1)/Q(2*j+1) for j in range(terms)), Q(0))
    tail = 2*u**(2*terms+1)/(Q(2*terms+1)*(1-u*u))
    return lower, lower+tail


def log_int_interval(n):
    exponent = n.bit_length()-1
    l2,h2 = log_atanh_interval(Q(2))
    lx,hx = log_atanh_interval(Q(n, 2**exponent))
    return exponent*l2+lx, exponent*h2+hx


def atan_center_error(x, terms=28):
    approx = sum(((-1)**j*x**(2*j+1)/Q(2*j+1)
                  for j in range(terms)), Q(0))
    return approx, x**(2*terms+1)/Q(2*terms+1)


def pi_center_error():
    a,ea = atan_center_error(Q(1,5))
    b,eb = atan_center_error(Q(1,239))
    return 16*a-4*b, 16*ea+4*eb


def exp_minus_i_taylor(theta, cutoff=40):
    real=imag=Q(0)
    power=Q(1)
    fact=1
    for k in range(cutoff+1):
        if k:
            power *= theta
            fact *= k
        if k % 4 == 0:
            real += power/fact
        elif k % 4 == 1:
            imag -= power/fact
        elif k % 4 == 2:
            real -= power/fact
        else:
            imag += power/fact
    return real,imag


def check():
    p,pe = pi_center_error()
    assert pe<Q(1,10**30)
    re=im=Q(0)
    error=Q(0)
    unit=10**12
    taylor_error=Q(100*4**41,factorial(41))
    assert taylor_error<Q(1,10**20)

    for n in range(5,101):
        ll,lh=log_int_interval(n)
        turns=round(20*log(n)/(2*pi))  # period choice only
        center=Q(10)*(ll+lh)-2*p*turns
        e=Q(10)*(lh-ll)+2*abs(turns)*pe
        theta=Q(round(center*unit),unit)
        angle_error=abs(center-theta)+e
        assert abs(theta)+angle_error<4
        x,y=exp_minus_i_taylor(theta)
        signweight=Q((-1)**(n-1),n*n)
        re += signweight*x
        im += signweight*y
        error += abs(signweight)*(angle_error+taylor_error)

    lower=Q(97,1000)
    assert re*re+im*im > lower*lower
    assert error<Q(1,1000)
    assert lower-Q(1,1000)-Q(1,100)>Q(2,25)
    print("PASS: 96 exact Q[i] phase enclosures")
    print("PASS: finite modulus > 97/1000; enclosure error < 1/1000")
    print("PASS: remaining infinite tail <= 1/100")
    print("COUNTEREXAMPLE: eta tail at s=2+20i after N=4")
    print("  modulus > 86/1000 > 2/25 (claimed bound)")


if __name__ == "__main__":
    check()
