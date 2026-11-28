"""Regression for exact overflow witnesses and quadratic norm formulas.
Not Agda or Lean acceptance. Use explicit require under python -O.
"""
from itertools import product
import sympy as s


def require(ok):
    if not ok:
        raise AssertionError('signed residue morphism')


def value(xs):
    return sum(x*3**j for j,x in enumerate(xs))


def add(c,x,y):
    if not x:
        return (),c
    total=x[0]+y[0]+c
    d=(total+1)%3-1
    z,k=add((total-d)//3,x[1:],y[1:])
    return (d,)+z,k


def mul(x,y):
    if not x:
        return (),0
    r,l=mul(x[1:],y[:-1])
    z,m=add(0,tuple(x[0]*e for e in y),(0,)+r)
    return z,m+l+value(x[1:])*y[-1]


def decode(v,n):
    if not n:
        return ()
    d=(v+1)%3-1
    return (d,)+decode((v-d)//3,n-1)


carry_count=mul_count=codec_count=0
for n in range(6):
    words=list(product((-1,0,1),repeat=n))
    p=3**n
    require(len({value(w)%p for w in words})==p)
    for x in words:
        require(decode(value(x)%p,n)==x)
        if n:
            require(value(x)==value(x[:-1])+3**(n-1)*x[-1])
        codec_count+=1
    for x,y in product(words,repeat=2):
        for c in (-1,0,1):
            z,k=add(c,x,y)
            require(value(x)+value(y)+c==value(z)+p*k)
            carry_count+=1
        z,k=mul(x,y)
        require(value(x)*value(y)==value(z)+p*k)
        require(decode((value(x)*value(y))%p,n)==z)
        if n:
            require(z[:-1]==mul(x[:-1],y[:-1])[0])
        mul_count+=1
# The two actual polynomial coefficient norm identities, over a generic
# commutative base. Valuation sharpness also needs noncancellation.
a,b,c,d,A,B=s.symbols('a b c d A B')
norm=lambda a,b:a*a+B*a*b-A*b*b
u,v=a*c+A*b*d,a*d+b*c+B*b*d
require(s.expand(norm(u,v)-norm(a,b)*norm(c,d))==0)
# F3 anisotropy for Gaussian residue, all eight nonzero classes.
for a,b in product(range(3),repeat=2):
    require(((a*a+b*b)%3==0)==(a==b==0))
# Generic integer valuation comparison on nonzero coefficient samples.
def v3(x):
    if not x:return float('inf')
    n=0
    while x%3==0:
        x//=3;n+=1
    return n
checks=0
for a,b in product(range(-50,51),repeat=2):
    if a==b==0:continue
    require(v3(a*a+b*b)==2*min(v3(a),v3(b)))
    require(v3(a*a-3*a*b+3*b*b)==min(2*v3(a),2*v3(b)+1))
    checks+=1
print(f'PASS {codec_count} signed residue round trips, {carry_count} carry witnesses, {mul_count} product witnesses, {checks} norm valuations; symbolic norm multiplicativity; F3 anisotropy')
