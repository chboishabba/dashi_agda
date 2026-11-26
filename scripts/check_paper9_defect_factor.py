#!/usr/bin/env python3
"""Exact right factor of Paper 9's cleared q-operator, no kernel claim."""
from fractions import Fraction as F
from sympy import symbols, expand, diff, Rational, __version__
x,y,e=symbols('x y e')
D=lambda f:expand(diff(f,x)*(e*x-y)/3+diff(f,y)*(e*y-x*x)/2+diff(f,e)*(e*e-x)/12)
u,v=D(x),D(y)
d=x**3-y*y; a=y*u-x*v; b=y*D(a)-2*a*v
p=[-5*y**3*d,72*x*(a*a+x*b)-108*x*d*a-46*x*y*y*d,108*x*x*y*(2*a-d),72*x**3*y*y]
q=[Rational(15,2)*y*y*((e*x-y)**2-d),-36*x*y*y*(e*x-y),36*x*x*y*y]
assert expand(D(u)-5*(e*e*x-2*e*y+x*x)/36)==0
assert expand(D(v)-7*(e*e*y-2*e*x*x+x*y)/24)==0
assert expand(D(D(u))-5*(e**3*x-3*e*e*y+3*e*x*x-x*y)/72)==0
for lhs,rhs in zip(p,[-q[2]*D(D(u))-q[1]*D(u)-q[0]*u,q[1]*u+2*x*q[0],3*u*q[2]+2*x*q[1],2*x*q[2]]):
    assert expand(lhs-rhs)==0
assert [c.subs({x:1,y:1,e:1}) for c in q]==[0,0,36]
print('8 exact symbolic operator/derivative/cusp controls PASS')
N=41
one=[F(1)]+[F(0)]*(N-1)
zero=[F(0)]*N
def sigma(n,k): return sum(i**k for i in range(1,n+1) if n%i==0)
def add(a,b): return [x+y for x,y in zip(a,b)]
def scale(c,a): return [c*x for x in a]
def sub(a,b): return add(a,scale(-1,b))
def mul(a,b): return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(N)]
def jet(a,k=1): return [n**k*v for n,v in enumerate(a)]
def poly(a,k):
    v=one
    for _ in range(k): v=mul(v,a)
    return v
X=[F(1)]+[F(240*sigma(n,3)) for n in range(1,N)]
Y=[F(1)]+[F(-504*sigma(n,5)) for n in range(1,N)]
E=[F(1)]+[F(-24*sigma(n,1)) for n in range(1,N)]
assert scale(12,jet(E))==sub(mul(E,E),X)
assert scale(3,jet(X))==sub(mul(E,X),Y)
assert scale(2,jet(Y))==sub(mul(E,Y),mul(X,X))
disc=sub(poly(X,3),poly(Y,2)); A=sub(mul(Y,jet(X)),mul(X,jet(Y))); B=sub(mul(Y,jet(A)),scale(2,mul(A,jet(Y))))
P3=scale(72,mul(poly(X,3),poly(Y,2)))
P2=scale(108,mul(mul(poly(X,2),Y),sub(scale(2,A),disc)))
P1=sub(sub(scale(72,mul(X,add(mul(A,A),mul(X,B)))),scale(108,mul(mul(X,disc),A))),scale(46,mul(mul(X,poly(Y,2)),disc)))
P0=scale(-5,mul(poly(Y,3),disc)); R=sub(mul(E,X),Y)
Q2=scale(36,mul(poly(X,2),poly(Y,2))); Q1=scale(-36,mul(mul(X,poly(Y,2)),R)); Q0=scale(F(15,2),mul(poly(Y,2),sub(mul(R,R),disc)))
def defect(f): return sub(scale(2,mul(X,jet(f))),mul(jet(X),f))
def P(f): return add(add(add(mul(P3,jet(f,3)),mul(P2,jet(f,2))),mul(P1,jet(f))),mul(P0,f))
def Q(s): return add(add(mul(Q2,jet(s,2)),mul(Q1,jet(s))),mul(Q0,s))
# Reverse-solve exact inverse X^3 (finite prefix only) then original hyper series.
x3=poly(X,3); inv=one[:]
for n in range(1,N): inv[n]=-sum(x3[i]*inv[n-i] for i in range(1,n+1))
z=mul(disc,inv)
assert z[0]==0
power=one; coeff=F(1); H=zero[:]; J=zero[:]
for n in range(N):
    H=add(H,scale(coeff,power)); J=add(J,scale(n*coeff,power))
    coeff*=F((6*n+1)*(2*n+1)*(6*n+5),72*(n+1)**3);power=mul(power,z)
assert P(H)==zero and defect(H)==zero and mul(H,H)==X
assert mul(X,jet(H))==mul(Y,J)
assert scale(6,mul(mul(H,Y),J))==scale(3,mul(X,jet(X)))
print(f'{N} degrees: original Ramanujan, hypergeometric ODE, signed defect, square and cleared jet PASS')
# Every coordinate impulse and both signs, including the zero mode.
for k in range(N):
    for sign in [-1,1]:
        f=zero[:]; f[k]=F(sign)
        assert P(f)==Q(defect(f))
        if k>0:
            assert P(f)[k]==72*k**3*sign
            assert Q(f)[k]==36*k*k*sign
            assert defect(f)[k]==2*k*sign
        else:
            assert P(f)[0]==Q(f)[0]==defect(f)[0]==0
print(f'{2*N} signed impulses, {2*N*N} operator coefficient comparisons PASS; SymPy {__version__}')
