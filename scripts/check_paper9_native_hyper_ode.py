#!/usr/bin/env python3
"""Exact arithmetic checks, not native proof-kernel acceptance."""
from fractions import Fraction as Q
from math import factorial
from sympy import symbols, expand, cancel, Rational, __version__

C = 640320**3
z0 = Q(-1728, C)
n = symbols('n')
assert expand(24*(2*n+1)*(6*n+1)*(6*n+5)-1728*(n**3+Rational(3,2)*n**2+Rational(23,36)*n+Rational(5,72))) == 0
x,y,dx,dy,d2x,d2y,f0,f1,f2,f3 = symbols('x y dx dy d2x d2y f0 f1 f2 f3')
a = y*dx-x*dy
b = y*(y*d2x-x*d2y)-2*a*dy
d = x**3-y**2
p=x/y; dp=a/y**2; d2p=b/y**3; z=d/x**3
L1=p*f1; L2=p**2*f2+p*dp*f1
L3=p**3*f3+3*p**2*dp*f2+p*(dp**2+p*d2p)*f1
P3=72*x**3*y**2
P2=108*x**2*y*(2*a-d)
P1=72*x*(a**2+x*b)-108*x*d*a-46*x*y**2*d
P0=-5*y**3*d
assert cancel(72*x**3*y**3*((1-z)*L3-z*(Rational(3,2)*L2+Rational(23,36)*L1+Rational(5,72)*f0))-(P3*f3+P2*f2+P1*f1+P0*f0)) == 0
assert [p.subs({x:1,y:1,dx:0,dy:0,d2x:0,d2y:0}) for p in [P3,P2,P1,P0]] == [72,0,0,0]
print('3 symbolic polynomial/constant controls PASS', flush=True)
for k in range(257):
    def t(i): return Q((-1)**i*factorial(6*i),factorial(3*i)*factorial(i)**3*C**i)
    assert (k+1)**3*t(k+1)==z0*(k**3+Q(3,2)*k*k+Q(23,36)*k+Q(5,72))*t(k)
print('257 original factorial recurrence checks PASS',flush=True)

# Independent finite formal power-series evaluator. Truncation is exact
# through N and must NOT be promoted to an all-index theorem.
N=32
one=[Q(1)]+[Q(0)]*N
zero=[Q(0)]*(N+1)
def add(a,b): return [u+v for u,v in zip(a,b)]
def scale(c,a): return [c*u for u in a]
def sub(a,b): return add(a,scale(-1,b))
def mul(a,b): return [sum((a[i]*b[j-i] for i in range(j+1)),Q(0)) for j in range(N+1)]
def power(a,k):
    r=one[:]
    for _ in range(k): r=mul(r,a)
    return r
def D(a,k=1): return [i**k*u for i,u in enumerate(a)]
def inv(a):
    r=[1/a[0]]
    for n in range(1,N+1): r.append(-sum(a[i]*r[n-i] for i in range(1,n+1))/a[0])
    return r
def sigma(n,k): return sum(i**k for i in range(1,n+1) if n%i==0)
X=[Q(1)]+[Q(240*sigma(n,3)) for n in range(1,N+1)]
Y=[Q(1)]+[Q(-504*sigma(n,5)) for n in range(1,N+1)]
E=[Q(1)]+[Q(-24*sigma(n,1)) for n in range(1,N+1)]
x2=power(X,2); x3=mul(x2,X); y2=power(Y,2); y3=mul(y2,Y)
d=sub(x3,y2); a=sub(mul(Y,D(X)),mul(X,D(Y))); b=sub(mul(Y,D(a)),scale(2,mul(a,D(Y))))
p3=scale(72,mul(x3,y2)); p2=scale(108,mul(mul(x2,Y),sub(scale(2,a),d)))
p1=sub(sub(scale(72,mul(X,add(mul(a,a),mul(X,b)))),scale(108,mul(mul(X,d),a))),scale(46,mul(mul(X,y2),d)))
p0=scale(-5,mul(y3,d)); ps=[p0,p1,p2,p3]
assert [p[0] for p in ps]==[0,0,0,72]
def residual(f):
    out=zero[:]
    for i,p in enumerate(ps): out=add(out,mul(p,D(f,i)))
    return out
# Three independent constructions: normalized binomial square root,
# direct composition of hypergeometric coefficients, and triangular ODE.
F=[Q(1)]
for n in range(1,N+1): F.append((X[n]-sum(F[k]*F[n-k] for k in range(1,n)))/2)
z=mul(d,inv(x3)); assert z[0]==0
h=one[:]; j=zero[:]; zp=one[:]; ck=Q(1)
for n in range(1,N+1):
    ck*=Q((6*n-5)*(2*n-1)*(6*n-1),72*n**3)
    zp=mul(zp,z)
    h=add(h,scale(ck,zp)); j=add(j,scale(n*ck,zp))
tri=one[:]
for n in range(1,N+1):
    tri[n]=-residual(tri)[n]/(72*n**3)
assert h==F==tri
assert mul(h,h)==X
assert scale(6,mul(mul(h,Y),j))==mul(X,scale(3,D(X)))
assert residual(h)==zero and residual(F)==zero and residual(tri)==zero
assert sub(sub(scale(3,D(X)),mul(E,X)),scale(-1,Y))==zero
assert sub(sub(scale(2,D(Y)),mul(E,Y)),scale(-1,x2))==zero
assert sub(sub(scale(12,D(E)),mul(E,E)),scale(-1,X))==zero
assert sub(sub(mul(Y,scale(3,D(X))),mul(X,scale(2,D(Y)))),d)==zero
for n in range(1,N+1):
    bad=h[:];bad[n]+=1
    r=residual(bad)
    assert r[:n]==zero[:n] and r[n]==72*n**3
print(f'{N+1} degrees: three independent coefficient constructions, square, cleared jet, 3 Ramanujan equations, bracket and ODE PASS',flush=True)
print(f'{N} single-coefficient perturbations rejected at first changed degree PASS',flush=True)
print('SymPy',__version__)

# Replay the actual finite-composition definitions (as opposed to the
# independent recursive inverse and square root above).
def compose(outer,inner):
    result=zero[:]; p=one[:]
    for k in range(N+1):
        assert all(v==0 for v in p[:k])
        result=add(result,scale(outer[k],p))
        p=mul(inner,p)
    return result
half=[Q(1)]
for k in range(N): half.append(Q(1-2*k,2*(k+1))*half[-1])
root2=compose(half,sub(X,one))
inv3=compose([Q(1)]*(N+1),sub(one,x3))
z2=mul(d,inv3)
assert mul(x3,inv3)==one and root2==F and z2==z
src=[Q((-1)**k*factorial(6*k),factorial(3*k)*factorial(k)**3*C**k) for k in range(N+1)]
outer=[v/z0**k for k,v in enumerate(src)]
assert compose(outer,z2)==h and compose(D(outer),z2)==j
for k in range(N):
    assert (k+1)**3*outer[k+1]==(k**3+Q(3,2)*k*k+Q(23,36)*k+Q(5,72))*outer[k]
assert D(mul(h,h))==add(mul(D(h),h),mul(h,D(h)))
assert mul(X,D(h))==mul(Y,j)
print(f'{N+1} degrees: literal finite compositions, zero-mode support, Leibniz and composed Euler-flow PASS',flush=True)
assert Q(256,7000)<Q(1,25) and Q(2688,35000)<Q(2,25)
assert ((1+Q(1,25))**3+(1+Q(2,25))**2-2)/(1-Q(1,25))**3==Q(1517,4608)<Q(1,3)
print('3 exact absolute composition budget inequalities/identity PASS',flush=True)
