"""Exact regression for source-specific cuts; no native kernel or PDE claim."""
from fractions import Fraction as Q
from itertools import product
import sympy as S

# NS: geometric far-cell inclusion, integer squared norms; no simulation.
ns=0
for k in product(range(-2,3),repeat=3):
    R2=sum(x*x for x in k)
    if not R2: continue
    for p in product(range(-5,6),repeat=3):
        d4=sum((2*x-y)**2 for x,y in zip(p,k))
        # |d| >= 2 |k|^(3/2), squared twice to avoid roots.
        if d4*d4 >= 256*R2**3:
            p2=sum(x*x for x in p); q2=sum((y-x)**2 for x,y in zip(p,k))
            assert p2*p2>=R2**3 and q2*q2>=R2**3
            ns+=1
R,L=S.symbols('R L',positive=True)
assert S.integrate(R**2,(R,1,L**S.Rational(2,3)))==(L**2-1)/3
print('NS far-cell geometry:',ns,'and exact volume integral')

# BSD: local primitive quartic obstruction mod 125 (2 and 10 classes).
M=125; squares={i*i%M for i in range(M)}
count=0
for d in (2,10):
    for u,v in product(range(M),repeat=2):
        if u%5==v%5==0: continue
        assert (d*u**4+(100//d)*v**4)%M not in squares
        count+=1
assert Q(75,8)**2==Q(25,4)**3-25*Q(25,4)
assert 25**2==5**3+100*5
# Actual E5 Euler coefficients, bad primes additive. Good primes counted.
a={1:1}
for n in range(2,21):
    z=1
    for p,e in S.factorint(n).items():
        if p in (2,5): z=0; break
        ap=p+1-(1+sum((y*y-x*x*x+25*x)%p==0 for x,y in product(range(p),repeat=2)))
        seq=[1,ap]
        for j in range(2,e+1): seq.append(ap*seq[-1]-p*seq[-2])
        z*=seq[e]
    a[n]=z
q=Q(5,6)
neg=sum((Q(-5*a[n],n*n)*q**n for n in range(2,21) if a[n]<0),Q(0))
tail=Q(10,21)*q**21/(1-q)
assert neg+tail<Q(1,4)
print('BSD primitive residues:',count,'coefficients:',a,'strict margin >',Q(1,4)-neg-tail)

# Hodge: separability idempotent in E tensor E, exact rational polynomial.
x,y=S.symbols('x y')
for f in (x**3+x*x-2*x-1,x**3-3*x+1,x**5+x**4-4*x**3-3*x*x+3*x+1):
    fy=f.subs(x,y)
    red=lambda z:S.rem(S.rem(S.expand(z),f,x),fy,y)
    e=red(S.cancel((f-fy)/(x-y))*S.invert(S.diff(fy,y),fy,y))
    assert red(e*e-e)==0
    assert red((x-y)*e)==0
    assert red(e-e.xreplace({x:y,y:x}))==0
    assert S.rem(e.subs(y,x),f,x)==1
print('Hodge: 12 exact field-separability identities')
