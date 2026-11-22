#!/usr/bin/env python3
"""RH selected four-window original-source horizontal mixed jet at q=4.

Exact local SymPy: retain original finite pole weight, even bump eps=E[Y^2]/2,
J2-moving mu, and physical off-line a=beta-1/2.
No positivity of actual selected finite-t W, zero census, or signed terminal.
"""
import sympy as s
x,L,m=s.symbols("x L m",real=True)
F=s.Rational
cs=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
ws=(s.Integer(1),s.Integer(-1),L,m)
def pair(w):
    d=s.diff(w,x,2)
    return (s.expand(sum(v*w.subs(x,c) for v,c in zip(ws,cs))),
            s.expand(sum(v*d.subs(x,c) for v,c in zip(ws,cs))))
A1,A1e=pair(s.cos(x)); A2,A2e=pair(s.cos(2*x))
M1,M1e=pair(x*x*s.cos(x)); M2,M2e=pair(x*x*s.cos(2*x))
J=s.expand(A1*M2-A2*M1)
Je=s.expand(A1e*M2+A1*M2e-A2e*M1-A2*M1e)
mu0=(13*L-8)/(144-54*L)
assert s.factor(J.subs(m,mu0))==0
mu1=s.factor(-Je.subs(m,mu0)/s.diff(J,m).subs(m,mu0))
assert s.factor((Je+s.diff(J,m)*mu1).subs(m,mu0))==0
def jet(v,ve,l):
    mm=mu0.subs(L,l)
    return (s.factor(v.subs({L:l,m:mm})),
            s.factor((ve+s.diff(v,m)*mu1).subs({L:l,m:mm})))
h,t=F(1,2),F(2,3)
def kern(w):
    w1,w1e=pair(s.cos(2*x)*w)
    w2,w2e=pair(s.cos(x)*w)
    return s.expand(4*(A1*w1-A2*w2)),s.expand(4*(A1e*w1+A1*w1e-A2e*w2-A2*w2e))
def pole(w):
    b1,b1e=pair(w*s.cos(16*x)*s.cos(x))
    b2,b2e=pair(w*s.cos(16*x)*s.cos(2*x))
    return s.expand(b1*A2-b2*A1),s.expand(b1e*A2+b1*A2e-b2e*A1-b2*A1e)
K0,Ke=kern(s.cos(4*x))
Kx,Kxe=kern(x*x*s.cos(4*x))
P0,P0e=pole(s.Integer(1))
P2,P2e=pole(32*x*x/s.pi**2)
kh,khe=jet(K0,Ke,h); kt,kte=jet(K0,Ke,t)
xh,xhe=jet(Kx,Kxe,h); xt,xte=jet(Kx,Kxe,t)
ph,phe=jet(P0,P0e,h); pt,pte=jet(P0,P0e,t)
ph2,ph2e=jet(P2,P2e,h); pt2,pt2e=jet(P2,P2e,t)
atomic_h2=s.factor(pt*xh-ph*xt)
smooth_h2=s.factor(pt*xhe+pte*xh-ph*xte-phe*xt)
smooth_t2=s.factor(pt2*khe+pt2e*kh-ph2*kte-ph2e*kt)
smooth_base=s.factor(pt*khe+pte*kh-ph*kte-phe*kt)
assert atomic_h2==0
assert smooth_h2==20*s.pi*(s.sqrt(3)+2*s.pi)/39
assert smooth_t2==640*(2*s.pi-s.sqrt(3))/(39*s.pi)
assert smooth_base==F(120,13)
# cosh(16*a*x/t)=1 + 128*a^2*x^2*u^2/pi^2+O(u^4)
off_line=s.factor(smooth_h2*128/s.pi**2)
assert off_line==2560*(s.sqrt(3)+2*s.pi)/(39*s.pi)
assert s.simplify(off_line)>0
print("PASS J2-preserving mu and original finite pole orientation")
print("PASS atomic [a²u²] = 0")
print("PASS epsilon[a²u²] = 2560*(sqrt(3)+2*pi)/(39*pi) > 0")
print("PASS epsilon[u²] = 640*(2*pi-sqrt(3))/(39*pi)")
print("PASS epsilon[constant] = 120/13")
print("OPEN uniform positive-R remainder, physical actual-zero sum, prime-side slack")
