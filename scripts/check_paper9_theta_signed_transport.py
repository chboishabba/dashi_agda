#!/usr/bin/env python3
"""Independent exact replay, not Agda/Lean acceptance."""
from itertools import product
from collections import Counter
from math import isqrt
import sympy as s

N = 64
checks = 0
def check(x):
    global checks
    assert x
    checks += 1

def mul(a, b):
    return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(N+1)]

def fourth(a):
    return mul(mul(a,a),mul(a,a))

def twist(a):
    return [(-1)**i*x for i,x in enumerate(a)]

f = [sum(k*k == n for k in range(-isqrt(N),isqrt(N)+1)) for n in range(N+1)]
h = [sum(k*(k+1) == n for k in range(N+1)) for n in range(N+1)]
B = fourth(f)
C = fourth(twist(f))
A = [0]+[16*x for x in fourth(h)[:-1]]
I = Counter(sum(x*x for x in v) for v in product(range(-8,9),repeat=4))
J = Counter(sum(x*x for x in v)//4 for v in product(range(-15,16,2),repeat=4))
mono = [0,16]+[0]*(N-1)
for n in range(N+1):
    check(B[n]==I[n])
    check(A[n]==J[n])
    check(C[n]==(-1)**n*B[n])
    check(B[n]==A[n]+C[n])
    check(mul(mono,fourth(h))[n]==A[n])
    check(mul(twist(f),twist(h))[n]==twist(mul(f,h))[n])

a,b,c,z = s.symbols('a b c z')
E4 = lambda a,b,c: (a*a+b*b+c*c)/2
E6 = lambda a,b,c: (a+b)*(b+c)*(c-a)/2
for E,k in [(E4,4),(E6,6)]:
    check(s.expand(E(-a,c,b)-E(a,b,c))==0)
    check(s.expand(E(-z*z*c,-z*z*b,-z*z*a)-z**k*E(a,b,c))==0)

Q=a*a-a*b+b*b
V=a*b*(b-a)
W=(a+b)*(2*a-b)*(a-2*b)
check(s.expand(4*Q**3-W**2-27*V**2)==0)
check(s.expand(E4(a,b,b-a)-Q)==0)
check(s.expand(E6(a,b,b-a)-W/2)==0)
print(f'{checks}/{checks} checks passed (degrees 0..{N}; exact integer and symbolic).')
