"""Independent exact replay of the signed row and Lambert cofinal geometry.

Finite diagnostics only; not an Agda kernel receipt.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as s

count_chart=0
for n in range(65):
    interval=[j for k in range(n) for j in (k,-k-1)]
    sym=interval+[n]
    assert sorted(sym)==list(range(-n,n+1))
    assert len(set(sym))==len(sym)
    assert sorted(-j for j in sym)==sorted(sym)
    count_chart+=3
x,y=s.symbols('x y',real=True)
a,b=s.symbols('a b',real=True)
for w in (4,6):
    assert s.expand((-x-s.I*y)**w-(x+s.I*y)**w)==0
    assert s.expand((-a*x-b-s.I*a*y)+(a*x+b+s.I*a*y))==0
print('chart',count_chart,'reflection symbolic',4)
def tri(n):
    return {(m,d) for r in range(1,n+1) for d in range(1,r+1) if r%d==0 for m in (r//d,)}
checks=0
for n,m in product(range(33),repeat=2):
    h=max(n,m)
    inner=tri(n)
    rect=set(product(range(1,n+1),range(1,h+1)))
    assert inner<=rect
    assert all(a*b<=n*h for a,b in rect)
    checks+=2
print('cofinal inclusions',checks)
count=0
for c,k in [(240,3),(504,5)]:
    for r in range(1,65):
        keys={(r//d,d) for d in range(1,r+1) if r%d==0}
        sigma=sum(d**k for d in range(1,r+1) if r%d==0)
        assert sum(c*d**k*Q(-1,2)**(m*d) for m,d in keys)==c*sigma*Q(-1,2)**r
        assert sum(c*d**k*Q(1,2)**(m*d) for m,d in keys)==c*sigma*Q(1,2)**r
        count+=2
    for n,m in product(range(1,13),repeat=2):
        h=max(n,m)
        i=tri(n); box=set(product(range(1,n+1),range(1,h+1))); o=tri(n*h)
        f=lambda p:c*p[1]**k*Q(-1,2)**(p[0]*p[1])
        b=lambda p:c*p[1]**k*Q(1,2)**(p[0]*p[1])
        assert abs(sum(map(f,box))-sum(map(f,i)))<=sum(map(b,o))-sum(map(b,i))
        count+=1
print('fibre and tail',count)
p=s.symbols('p',nonzero=True)
for k,z,f in [(4,p**4/90,45/p**4),(6,p**6/945,s.Rational(945,2)/p**6)]:
    assert s.simplify(f*2*z-1)==0
print('normalization',2)
