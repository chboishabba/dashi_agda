#!/usr/bin/env python3
"""S4 selected ORIGINAL E:y²=x³-x same-L eta bridge regression.
Finite tests cannot prove modularity or isogeny invariance: see proof note.
"""
from fractions import Fraction as Q
import sympy as sp
import mpmath as mp

x,y,X=sp.symbols('x y X',nonzero=True)
u=x-1/x
v=y*(1+1/x**2)
assert sp.cancel((x**3-x)*(1+1/x**2)**2 - (u**3+4*u))==0
assert sp.cancel(v**2-(u**3+4*u) -(y**2-(x**3-x))*(1+1/x**2)**2)==0
assert sp.expand(x*(u-X))==x**2-X*x-1
assert sp.discriminant(x**2-X*x-1,x)==X**2+4
print('PASS original-curve exact rational two-isogeny polynomial identity, generic degree 2')

def points(p,a):
    ys=[0]*p
    for y0 in range(p):ys[(y0*y0)%p]+=1
    return 1+sum(ys[(z*z*z+a*z)%p] for z in range(p))

def eta_coeffs(k):
    a=[0]*(k+1);a[1]=1
    for step in list(range(4,k+1,4))+list(range(8,k+1,8)):
        b=a[:]
        for i in range(step,k+1):b[i]-=2*a[i-step]
        for i in range(2*step,k+1):b[i]+=a[i-2*step]
        a=b
    return a

a=eta_coeffs(300)
primes=list(sp.primerange(3,300))
for p in primes:
    assert points(p,-1)==points(p,4)
    assert p+1-points(p,-1)==a[p]
assert [a[i] for i in [1,5,9,13,17,21,25]]==[1,-2,-3,6,2,0,-1]
print('PASS',len(primes),'good-prime E/Eprime/isogeny/eta q-coefficient comparisons')

assert 1-Q(2,15)-Q(2,255)==Q(73,85)
ct=0
for q in [Q(0),Q(1,10**9),Q(1,128),Q(1,32),Q(1,16)]:
    P=Q(1)
    for n in range(1,15):
        P*=(1-q**n)**2*(1-q**(2*n))**2
        assert Q(73,85)<=P<=1
        tail=2*Q(1,16)**(n+1)/(1-Q(1,16))+2*Q(1,16)**(2*n+2)/(1-Q(1,16)**2)
        M=P
        for k in range(n+1,60):M*=(1-q**k)**2*(1-q**(2*k))**2
        assert 0<=P-M<=tail
        ct+=1
print('PASS',ct,'exact rational all-factor positive-product and tail-envelope samples')

mp.mp.dps=55
def f(t,N):
    q=mp.exp(-8*mp.pi*t);prod=mp.mpf(1)
    for k in range(1,N+1):prod*=(1-q**k)**2*(1-q**(2*k))**2
    return mp.exp(-2*mp.pi*t)*prod
for t in map(mp.mpf,['0.05','0.08','0.1','0.2','0.3','0.8','1.9']):
    lhs=f(1/(32*t),320);rhs=32*t*t*f(t,320)
    assert abs(lhs-rhs)<mp.mpf('1e-45')*max(abs(lhs),abs(rhs))
print('PASS seven high-precision eta Fricke transformation samples')
L=4*mp.pi*mp.quad(lambda t:f(t,70),[1/mp.sqrt(32),1,3,mp.inf])
B=mp.beta(mp.mpf('0.5'),mp.mpf('0.25'))/8
LB=mp.mpf(146)/85*mp.exp(-2*mp.pi/mp.sqrt(32))
assert abs(L-B)<mp.mpf('1e-44') and 0<LB<L
print('PASS numerical original curve Mellin/Beta identity L(E,1) =',mp.nstr(L,47))
print('PASS symbolic universal lower bound (146/85)*exp(-2pi/sqrt(32)); numeric',mp.nstr(LB,25))
print('FIREWALL external modularity/isogeny invariance are cited classical theorems; Agda/Lean native proof, BSD S6 OPEN')
