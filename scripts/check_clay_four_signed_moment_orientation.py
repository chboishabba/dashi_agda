"""Exact finite regressions for the unbounded-degree algebra and rank-six sign cut."""
from itertools import combinations
from fractions import Fraction as Q
import sympy as sp

checks = 0

def require(ok):
    global checks
    if not ok:
        raise AssertionError('signed source regression failed')
    checks += 1

a,b,x = sp.symbols('a b x')
h = [sp.Integer(1)]
quot = sp.Integer(1)
for n in range(9):
    h.append(sp.expand(a*h[-1]+b**(n+1)))
    if n:
        quot = sp.expand(a*b*quot+h[n]*x**n)
    d = h[n]*x**(n+2)-h[n+1]*x**(n+1)+(a*b)**(n+1)
    require(sp.expand(d-(x-a)*(x-b)*quot)==0)
    require(all(c>0 for c in sp.Poly(quot,a,b,x).coeffs()))

# Actual shape controls, not an elliptic-curve measure. Three atoms with
# zero total mass: changing the first moment does not change the crossings.
for p in (Q(1,4), Q(1,2), Q(3,4)):
    M = [Q(0)] + [p*2**j-1 for j in range(1,10)]
    require(M[1] == 2*p-1)
    for j in range(1,9):
        aa,bb=Q(1,2),Q(3,2)
        hh=lambda k: sum(aa**i*bb**(k-i) for i in range(k+1))
        require(hh(j-1)*M[j+1]-hh(j)*M[j]>0)
        if M[j]>=0:
            require(M[j+1]>0)

# All proper nonempty distinct support masks have a determinant+1
# diagonal sign flip which negates that coefficient.
axes=set(range(6))
for mask in range(1,63):
    s={i for i in axes if mask>>i&1}
    i=min(s); j=min(axes-s)
    signs=[-1 if k in (i,j) else 1 for k in axes]
    require(sp.prod(signs)==1 and sp.prod(signs[k] for k in s)==-1)
for i,j in combinations(sorted(axes),2):
    require(sp.prod(-1 if k in (i,j) else 1 for k in axes)==1)
print(f'{checks}/{checks} exact algebra/shape controls PASS')
