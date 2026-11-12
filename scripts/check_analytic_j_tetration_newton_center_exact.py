#!/usr/bin/env python3
"""Finite exact-rational Newton-center evidence for the selected exponential fixed point.

An independent numerical/interval *preflight*, not an Agda/Bishop fixed-point
inhabitant. No floats enter any asserted comparison. Original exponential,
cosine and sine Taylor series have explicit rational remainders.

At a = 31813/100000, b = 133724/100000:
exp(a) uses positive terms and a geometric remainder bound;
cos(b), sin(b) use alternating decreasing terms (b^2 < 2).
Consequently all enclosed values contain the true analytic values.

Remaining Bishop integration: bridge exact rational intervals to the
original Bishop exponential/cosine/sine, prove complex line-integral
derivative bound in Bishop metrics, and apply original constructive
completeness/Banach without assuming the fixed point.
"""
from fractions import Fraction as Q
from math import factorial

A, B, R = Q(31813, 100000), Q(133724, 100000), Q(1, 200)

def exp_interval(x, n=24):
    assert 0 <= x < n + 2
    prefix = sum((x**k / factorial(k) for k in range(n+1)), Q(0))
    # For k>=n+1, each next/current ratio <= x/(n+2).
    tail = x**(n+1) / factorial(n+1) / (1-x/Q(n+2))
    return prefix, prefix+tail

def cos_interval(x, n=24):
    assert 0 <= x*x < 2  # decreasing absolute Taylor terms
    prefix = sum(((-1)**k*x**(2*k)/factorial(2*k)
                  for k in range(n+1)), Q(0))
    tail = x**(2*n+2)/factorial(2*n+2)
    return prefix-tail, prefix+tail

def sin_interval(x, n=24):
    assert 0 <= x*x < 2
    prefix = sum(((-1)**k*x**(2*k+1)/factorial(2*k+1)
                  for k in range(n+1)), Q(0))
    tail = x**(2*n+3)/factorial(2*n+3)
    return prefix-tail, prefix+tail

def mul(lhs, rhs):
    corners = [a*b for a in lhs for b in rhs]
    return min(corners), max(corners)

def sub(lhs, rhs):
    return lhs[0]-rhs[1], lhs[1]-rhs[0]

def square_lower(interval):
    a,b=interval
    return Q(0) if a<=0<=b else min(a*a,b*b)

def square_upper(interval):
    a,b=interval
    return max(a*a,b*b)

e, cosine, sine = exp_interval(A), cos_interval(B), sin_interval(B)
re, im = mul(e,cosine), mul(e,sine)
res_re, res_im = sub(re,(A,A)), sub(im,(B,B))
den_re = sub(re,(Q(1),Q(1)))
residual_norm_sq_upper = square_upper(res_re)+square_upper(res_im)
derivative_norm_sq_lower = square_lower(den_re)+square_lower(im)
center_norm_sq = A*A+B*B

assert residual_norm_sq_upper < Q(1,10000)**2
assert derivative_norm_sq_lower > Q(3,2)**2
assert exp_interval(A+R)[1] < Q(7,5)
assert Q(271,200)**2 < center_norm_sq < Q(11,8)**2

# In the future Bishop analytic derivative layer:
# |T'(z)| <= exp(Re(p0)+R)*R / |exp(p0)-1| < 7/1500 < 1/200.
assert Q(7,5)*R/Q(3,2) < Q(1,200)
# Center displacement + contraction*radius < radius proves invariant disk.
assert Q(1,10000)/Q(3,2) + Q(1,200)*R < R

# Corrected Koenigs disk: 1/10, not the original invalid 1/8.
assert Q(27,20)-Q(1,10) == Q(5,4)
assert Q(5,4)*Q(4,5) == 1
assert Q(2)*Q(5,4)**2*Q(8,25) == 1
assert Q(69,50)*Q(4,5)**2 == Q(552,625) < 1
assert Q(69,50)*Q(8,25)*Q(1,10)**2 < Q(7,1000)

# Reject the original 1/8 disk with only 2499/2000 lower modulus:
assert Q(4,5)*Q(2499,2000) < 1
print("PASS: exact Taylor enclosure residual norm squared < (1/10000)^2")
print("PASS: |exp(p0)-1| > 3/2 and exp(Re(p0)+1/200) < 7/5")
print("PASS: rational Newton disk self-map/contraction sufficient inequalities")
print("PASS: corrected Koenigs radius=1/10 and beta=552/625")
print("OPEN: Bishop analytic exponent/derivative source weld and Banach inhabitant")
