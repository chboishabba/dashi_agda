#!/usr/bin/env python3
"""RH theta=pi/13 & original 27->13->26 native source audit.
Local exact SymPy/rational and 27-site exhaustive test. Source owners:
Lean RiemannProjectiveQuarticFourWindowAtomic / PoleSameObject / SignedPoleTarget;
Agda BalancedTernaryAntipodalOrbitExact and native projective13 orientation;
Griess order13 linear grade action. Not a Lean/Agda/RH kernel proof.
"""
from itertools import combinations,product
from fractions import Fraction as F
import sympy as s
R=s.Rational
z,u,p,L,m=s.symbols("z u p L m",real=True)
b=2*z*z-1
A1,A2=1-z-m,1-b-L+m
M1,M2=-u*z-m,-u*b-L/4+m
J=s.expand(A1*M2-A2*M1)
assert s.diff(J,m,2)==0
mu0=s.factor(-J.subs(m,0)/s.diff(J,m))
pole=s.expand((A1+(1-p)*z)*A2-(A2+(1-p)*b)*A1)
Qtheta=4*(z*A2-b*A1)
assert s.simplify(pole-(1-p)*Qtheta/4)==0
l1,l2,m1,m2=s.symbols("l1 l2 m1 m2")
P1=pole.subs({L:l1,m:m1}); P2=pole.subs({L:l2,m:m2})
V1=Qtheta.subs({L:l1,m:m1});V2=Qtheta.subs({L:l2,m:m2})
assert s.simplify(P2*V1-P1*V2)==0
def endpoint(lam):
    mm=s.factor(mu0.subs(L,lam))
    aa=A1.subs({L:lam,m:mm});bb=A2.subs({L:lam,m:mm})
    PP=s.factor(pole.subs({L:lam,m:mm}))
    v=[4*(aa-bb),4*(z*bb-b*aa),-4*lam*aa,4*mm*(aa+bb)]
    assert s.simplify(sum(v))==0
    assert s.simplify(v[1]*u+v[2]/4+v[3])==0
    return mm,PP,v
half,two=endpoint(R(1,2)),endpoint(R(2,3))
vec=[s.factor(two[1]*half[2][i]-half[1]*two[2][i]) for i in range(4)]
C=s.factor(-vec[3])
assert vec[1]==0
assert s.simplify(vec[0]+3*C)==0 and s.simplify(vec[2]-4*C)==0
assert s.simplify(C.subs({z:R(1,2),u:R(1,9),p:-R(1,2)})-R(40,351))==0
# Closed angle-dependent projective scalar. This factorization shows
# its 13-axis sign directly from rational cos(pi/13) bounds.
D_two=4*u*z*z+2*u*z-2*u-4*z*z-2*z+5
D_half=16*u*z*z+8*u*z-8*u-16*z*z-8*z+21
Cfactor=4*(p-1)*(z-1)*(2*z+1)*(4*z*z+2*z-5)*(
    6*z*z+3*z-7)*(u*z-z+1)/(9*D_two*D_half)
assert s.simplify(C-Cfactor)==0
q=s.symbols("q",real=True)
Fourier=C*(-3+4*s.cos(s.pi*q/2)-s.cos(s.pi*q))
assert s.simplify(s.trigsimp(Fourier+2*C*(1-s.cos(s.pi*q/2))**2))==0
assert s.simplify(Fourier.subs(q,4))==0
# Certified rational cosine interval from 157/50 < pi <22/7 and
# alternating cosine Taylor for 0<pi/13<1/4.
amin,amax=F(157,650),F(22,91)
zlo,zhi=F(9708,10000),F(971,1000)
assert zlo<1-amax**2/2+amax**4/24-amax**6/720
assert 1-amin**2/2+amin**4/24<zhi
U=F(1,169)
def N(l,z):return 4*l*U*z-l*z+l+8*U*z*z-4*U*z-4*U
def D(l,z):return -3*l+8*U*z*z+4*U*z-4*U-8*z*z-4*z+12
assert 4*U*zlo-zlo+1>0                 # N increases in lambda
assert -F(1,2)+4*F(1,2)*U+16*U*zhi-4*U<0  # N decreases in z
assert 16*U*zlo+4*U-16*zlo-4<0        # D decreases in z
assert N(F(1,2),zhi)>0 and D(F(1,2),zlo)<0
assert 10*N(F(2,3),zlo) < -D(F(1,2),zlo)
assert 2-2*zlo*zlo-F(1,2)<0 and 2*zlo*zlo-1>0
# All lambda in [1/2,2/3] have mu in (-1/10,0), A1>0, A2<0,
# and hence pole=(1-cos16theta)*(zA2-bA1)<0 at theta=pi/13.
assert 4*R(zlo)**2+2*R(zlo)-5>0
assert 6*R(zlo)**2+3*R(zlo)-7>0
assert 1-R(zhi)+R(zlo)/169>0
# These inequalities together with both negative endpoint denominators
# show C(pi/13)>0, although the pole coordinates are negative.
# The real original 27-point grade action, not a synthetic 13 label.
V=tuple(product(range(3),repeat=3));O=(0,0,0)
def M(x):
    a,b,c=x
    return ((a+b)%3,(b+c)%3,(a+b+c)%3)
def antipode(x):return tuple((-a)%3 for a in x)
def lift(x):return antipode(M(x))
def orbit(x,act):
    out=[x];y=act(x)
    while y!=x:
        assert y not in out
        out.append(y);y=act(y)
    return out
assert len(V)==27 and len(orbit(O,lift))==1
assert all(len(orbit(x,M))==13 and len(orbit(x,lift))==26
           and orbit(x,lift)[13]==antipode(x) for x in V if x!=O)
assert len({min(x,antipode(x)) for x in V if x!=O})==13
def adjacent(x,y):
    return sum(a!=b for a,b in zip(x,y))==1 and all(
        a==b or a==0 or b==0 for a,b in zip(x,y))
edges=[(x,y) for x,y in combinations(V,2) if adjacent(x,y)]
assert len(edges)==54
assert sum(adjacent(M(x),M(y)) for x,y in edges)==0
assert sum(adjacent(lift(x),lift(y)) for x,y in edges)==0
# pi/2 is 13/2 times pi/13: no SINGLE C26 integer-step angular chart
# contains all original four source centres unchanged.
assert all(2*k-13!=52*j for k in range(26) for j in range(-2,3))
print("PASS arbitrary theta: pole proportional to theta source; exact projective cancellation")
print("PASS any J2-null endpoints => (-3,0,4,-1), same pi/2 biharmonic Fourier symbol")
print("PASS theta=pi/13 full original lambda corridor: mu in (-1/10,0), pole NEGATIVE")
print("PASS 27=1+2*13: true original C13 action, C26 antipodal lift, order 26")
print("PASS 54 original spatial cube edges lost under C13 and C26 actions")
print("PASS pi/2 not on pi/13 angular integer grid; true C26 spatial weld OPEN")
print("OPEN positive-pole redesigned witness, finite-R,t and signed actual-zero terminal")
