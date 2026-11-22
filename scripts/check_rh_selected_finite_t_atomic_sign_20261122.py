#!/usr/bin/env python3
"""DASHI RH selected four-window source: finite-t atomic sign stress (SymPy).

Exact ORIGINAL source formula donors (dashi_lean4/main):
 RiemannProjectiveQuarticFourWindowAtomic[.lean]
 RiemannProjectiveQuarticFourWindowAtomicPoleSign.lean
 RiemannProjectiveQuarticFourWindowPoleSameObject.lean
 RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean
 RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean

This tests the *atomic zero-radius model with atomic mu endpoints*, not
positive-R source W, not physical zeta zeros and not a universal signed gap.
"""
import sympy as s
from sympy import Rational as F
from math import factorial

u,a,q=s.symbols('u a q',real=True)
Lhalf,Ltwo=F(1,2),F(2,3)
centres=(F(0),F(1,3),F(1,2),F(1)) # multiples of pi
mu=lambda L:(13*L-8)/(144-54*L)
A1=lambda L:F(1,2)-mu(L)
A2=lambda L:F(3,2)-L+mu(L)
coeff=lambda L:(s.Integer(1),s.Integer(-1),L,mu(L))
assert mu(Lhalf)==-F(1,78)
assert mu(Ltwo)==F(1,162)
J2=lambda L:-s.pi**2*(54*L*mu(L)+13*L-144*mu(L)-8)/72
assert J2(Lhalf)==J2(Ltwo)==0

def atom_profile(L,qvalue,cosh_weight):
    return 4*sum(w*(A1(L)*s.cos(2*s.pi*z)-A2(L)*s.cos(s.pi*z))
                 *s.cos(qvalue*s.pi*z)*cosh_weight(z)
                 for w,z in zip(coeff(L),centres))

Pinf=lambda L:3*(2-L)/4
Kinf=lambda av,qv:s.expand(Pinf(Ltwo)*atom_profile(Lhalf,qv,lambda z:s.cosh(16*av*s.pi*z))
                          -Pinf(Lhalf)*atom_profile(Ltwo,qv,lambda z:s.cosh(16*av*s.pi*z)))
# av is physical beta-1/2, not normalized alpha. In high t limit fixed
# alpha=16*av/t goes to zero. For independent normalized alpha, use below.
h=s.symbols('h',positive=True)
Knormalized=lambda al,qv:s.expand(Pinf(Ltwo)*atom_profile(Lhalf,qv,lambda z:s.cosh(al*s.pi*z))
                          -Pinf(Lhalf)*atom_profile(Ltwo,qv,lambda z:s.cosh(al*s.pi*z)))
al=s.symbols('alpha',real=True)
Kexact=Knormalized(al,q)
formula= F(160,351)*s.cos(s.pi*q/2)*s.cosh(s.pi*al/2) \
        -F(40,351)*s.cos(s.pi*q)*s.cosh(s.pi*al)-F(40,117)
assert s.trigsimp(Kexact-formula)==0
Kbase=s.trigsimp(Kexact.subs(al,0))
assert s.trigsimp(Kbase+F(80,351)*(1-s.cos(s.pi*q/2))**2)==0
# For alpha!=0, high-t pole model itself admits positive lobes between
# two exact horizontal q=4k negative points.
x=s.symbols('x',real=True)
Q=s.factor((4*h*x-(2*x*x-1)*(2*h*h-1)-3))
xstar=h/(2*h*h-1)
assert s.simplify(s.diff(Q,x).subs(x,xstar))==0
Qmax=s.factor(Q.subs(x,xstar))
assert s.factor(Qmax-4*(h*h-1)**2/(2*h*h-1))==0
assert s.factor(Q.subs(x,1)+2*(h-1)**2)==0
# For every h>1, xstar lies within (0,1) and Qmax>0;
# Q(1)<0. This is an analytic witness, not a zero census.

# ORIGINAL FINITE-t atomic pole responses (not high-limit pole):
# B1=1+h1/4-mu*h3; B2=1-h1/4-lambda*h2+mu*h3;
# P_t=B1*A2-B2*A1. Let u=pi/t and alpha=16*a/t.
def cosh6(c):
    return sum((c*u)**(2*j)/factorial(2*j) for j in range(4))
h1,h2,h3=cosh6(F(8,3)),cosh6(4),cosh6(8)
def Pfinite(L):
    B1=1+h1/4-mu(L)*h3
    B2=1-h1/4-L*h2+mu(L)*h3
    return s.expand(B1*A2(L)-B2*A1(L))
def finite_profile(L,qv):
    return s.expand(atom_profile(L,qv,lambda z:cosh6(16*a*z)))
def finite_k(qv):
    return s.Poly(Pfinite(Ltwo)*finite_profile(Lhalf,qv)
        -Pfinite(Lhalf)*finite_profile(Ltwo,qv),u)
K4=finite_k(s.Integer(4))
assert K4.nth(0)==0 and K4.nth(2)==0
quartic=s.factor(K4.nth(4))
assert s.simplify(quartic-F(5120,351)*(1-16*a**4))==0
assert s.factor(quartic.subs(a,F(1,4))-F(1600,117))==0
# For each fixed |a|<1/2, q=4 positive for all sufficiently large t:
# since series leading coefficient in u^4 is strictly positive.
# For q=1, zeroth coefficient is negative, independent of a.
K1=finite_k(s.Integer(1))
assert K1.nth(0)==-F(80,351)
# At normalized q=0 an off-ordinate zero is excluded; the same-object
# atomic test predicts the leading horizontal sign <0 for a!=0.
K0=finite_k(s.Integer(0))
assert K0.nth(0)==0 and K0.nth(2)==0
assert s.simplify(K0.nth(4)+F(81920,351)*a**4)==0

# Rigorous rational sign of LEADING orders at representative physical a.
for aa in (F(0),F(1,16),F(1,4),F(49,100)):
    assert quartic.subs(a,aa)>0
    assert K1.nth(0)<0
# Horizontal reflection beta -> 1-beta is a->-a; its response is even.
for c in [K4.nth(0),K4.nth(2),K4.nth(4),K4.nth(6),K1.nth(0),K1.nth(2)]:
    assert s.simplify(c.subs(a,-a)-c)==0

# Numeric high-precision *stress* (not rigorous interval enclosure) of
# exact untruncated cosh model using same source formulas.
t=s.symbols('t',positive=True)
H1=s.cosh(8*s.pi/(3*t)); H2=s.cosh(4*s.pi/t); H3=s.cosh(8*s.pi/t)
def exact_pole(L):
    return (1+H1/4-mu(L)*H3)*A2(L) - (1-H1/4-L*H2+mu(L)*H3)*A1(L)
def Kexact_physical(tvalue,av,qv):
    r=s.Integer(tvalue); aa=s.Rational(av)
    physical=lambda L:atom_profile(L,s.sympify(qv),lambda z:s.cosh(16*aa*s.pi*z/r))
    val=exact_pole(Ltwo)*physical(Lhalf)-exact_pole(Lhalf)*physical(Ltwo)
    return s.N(val.subs(t,r),55)
count=0
for tt in (200,400,1000,10000):
    for aa in (F(0),F(1,16),F(1,4),F(49,100)):
        positive=Kexact_physical(tt,aa,4)
        negative=Kexact_physical(tt,aa,1)
        assert positive>0 and negative<0
        count+=1
# Strict positive in physical atomic limit does NOT imply smoothed source W
# survives the perturbation. In fact its leading margin falls like t^-4.
assert s.limit(quartic.subs(a,F(1,4))*(s.pi/t)**4,t,s.oo)==0

print('PASS exact high-t selected atomic K0=-80/351*(1-cos(pi*q/2))^2')
print('PASS high-limit horizontal positive lobe and negative q=4k controls')
print('PASS finite-t atomic q=4 coefficient: (5120/351)*(1-16*a^4)*(pi/t)^4')
print('PASS q=1 zeroth coefficient -80/351; q=0 quartic horizontal negative')
print('PASS 16/16 actual finite-t atomic high-precision sign stress pairs')
print('OPEN: finite positive-R source W sign and actual-zeta signed high terminal')

# Original Agda and Lean BIDI marked-fourth producer (already source-owned):
# P4(a,d) = [P4(a-A,d)+P4(a+A,d)]/2
#          -3 A^2 [P2(a-A,d)+P2(a+A,d)] + 5 A^4.
# M0,M2,M4 are independent; zeroth and second alone do not buy the sign.
A,xx,dd=s.symbols('A xx dd',real=True)
P2=lambda x,d:x**2-d**2
P4=lambda x,d:x**4-6*x**2*d**2+d**4
bidi=(P4(xx-A,dd)+P4(xx+A,dd))/2 \
    -3*A**2*(P2(xx-A,dd)+P2(xx+A,dd))+5*A**4
assert s.expand(P4(xx,dd)-bidi)==0
cfg0=[s.Integer(-1),s.Integer(-1),s.Integer(1),s.Integer(1)]
cfg1=[-s.sqrt(2),s.Integer(0),s.Integer(0),s.sqrt(2)]
assert len(cfg0)==len(cfg1)==4
assert sum(y**2 for y in cfg0)==sum(y**2 for y in cfg1)==4
assert sum(y**4 for y in cfg0)==4
assert sum(y**4 for y in cfg1)==8
assert sum(P4(0,y) for y in cfg0)<6<sum(P4(0,y) for y in cfg1)
print('PASS original 0/2/4 even-marked BIDI identity; same M0/M2 opposite fourth-threshold controls')
