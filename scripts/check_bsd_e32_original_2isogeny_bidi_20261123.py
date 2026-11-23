#!/usr/bin/env python3
"""Original E32 y^2=x^3-x: exact degree-2 rational isogeny and dual.

Rational functions checked in Q(E), exceptional kernels/O checked separately,
then independently finite-field group homomorphisms and dual composition.
This does NOT establish Selmer, Sha, the general rank formula or BSD.
"""
import sympy as s
from fractions import Fraction

x,y,X,Y=s.symbols('x y X Y')
f=x-1/x; g=y*(1+1/x**2)
F=(f,g)
H=((X+4/X)/4, Y*(1-4/X**2)/8)

def clear_curve_relation(expr, curve, y2):
    num=s.cancel(expr).as_numer_denom()[0]
    # The identities are degree <=2 in y/Y after clearing denominator.
    poly=s.Poly(s.expand(num),curve)
    _, rem=s.div(poly, s.Poly(curve*curve-y2,curve))
    assert s.simplify(rem.as_expr())==0, rem

clear_curve_relation(g**2-f**3-4*f,y,x**3-x)
clear_curve_relation((H[1]**2-(H[0]**3-H[0])),Y,X**3+4*X)
comp=(s.cancel(H[0].subs({X:f,Y:g})),s.cancel(H[1].subs({X:f,Y:g})))
dupx=(x*x+1)**2/(4*x*(x*x-1))
dupy=((3*x*x-1)/(2*y))*(x-dupx)-y
assert s.factor(comp[0]-dupx)==0
clear_curve_relation(comp[1]-dupy,y,x**3-x)
# Exact reverse composition on the original partner Eprime, not just finite rows.
compdual=(s.cancel(f.subs(x,H[0])),s.cancel(g.subs({x:H[0],y:H[1]})))
dualdupX=(3*X**2+4)**2/(4*(X**3+4*X))-2*X
dualdupY=((3*X**2+4)/(2*Y))*(X-dualdupX)-Y
assert s.factor(compdual[0]-dualdupX)==0
clear_curve_relation(compdual[1]-dualdupY,Y,X**3+4*X)
# The dual genuinely has degree 2 and is defined on E' (including its O).
# phi: E -> E' with ker={O,(0,0)}.  phihat: E' -> E with ker={O,(0,0)}.
# On E 2-torsion x=+-1: phi(P)=(0,0), then phihat=(O).
assert f.subs(x,1)==0 and f.subs(x,-1)==0
assert s.simplify(g.subs({x:1,y:0}))==0
assert s.simplify(H[0].subs({X:2,Y:4})-1)==0
assert s.simplify(H[1].subs({X:2,Y:4}))==0

O=None

def inv(a,p):return pow(a%p,-1,p)
def add(P,Q,a,p):
    if P is O:return Q
    if Q is O:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return O
    if x1==x2:
        slope=((3*x1*x1+a)*inv(2*y1,p))%p
    else:slope=((y2-y1)*inv(x2-x1,p))%p
    xr=(slope*slope-x1-x2)%p
    yr=(slope*(x1-xr)-y1)%p
    return xr,yr

def points(a,b,p):
    return [O]+[(xx,yy) for xx in range(p) for yy in range(p)
                if (yy*yy-xx**3-a*xx-b)%p==0]

def phi(P,p):
    if P is O or P==(0,0):return O
    xx,yy=P;return ((xx-inv(xx,p))%p,(yy*(1+inv(xx*xx,p)))%p)
def phihat(P,p):
    if P is O or P==(0,0):return O
    xx,yy=P
    return (((xx+4*inv(xx,p))*inv(4,p))%p,
            (yy*(1-4*inv(xx*xx,p))*inv(8,p))%p)

checks=0
for p in [3,5,7,11,13,17,19,23,29,31,37]:
    # The degree-2 isogenies have good reduction for every odd p.
    ps=points(-1,0,p); qs=points(4,0,p)
    assert all(Q is O or (Q[1]*Q[1]-Q[0]**3-4*Q[0])%p==0 for Q in (phi(P,p) for P in ps))
    assert all(Q is O or (Q[1]*Q[1]-Q[0]**3+Q[0])%p==0 for Q in (phihat(P,p) for P in qs))
    for P in ps:
        assert phihat(phi(P,p),p)==add(P,P,-1,p)
        for R in ps:
            assert phi(add(P,R,-1,p),p)==add(phi(P,p),phi(R,p),4,p)
            checks+=1
    for P in qs:
        assert phi(phihat(P,p),p)==add(P,P,4,p)
        for R in qs:
            assert phihat(add(P,R,4,p),p)==add(phihat(P,p),phihat(R,p),-1,p)
            checks+=1
    print('p',p,'E(Fp)',len(ps),'Eprime(Fp)',len(qs),'hom/dual PASS')
print('PASS exact rational function field forward/dual compositions, all exceptional 2-torsion,',checks,'independent group law pairs')

# Exact selected rank-zero *classical* descent, invoking Tate's
# two-isogeny theorem (not a locally proved Agda theorem):
#   2^(r+2) = |alpha_E(E(Q))| * |alpha_Eprime(Eprime(Q))|.
# Prime-support: any x square class in alpha(y^2=x^3+a*x^2+b*x)
# has a squarefree representative dividing b. For b=-1 only +-1;
# for b'=4 only +-1, +-2. Eprime real equation X*(X^2+4)>=0
# excludes X<0; exceptional X=0 has class b'=4=1.
E_candidates={-1,1}
Eprime_candidates={-2,-1,1,2}
E_actual={1,-1}  # O and T=(0,0) with b=-1
Eprime_actual={1,2}  # O and rational point (2,4); X cannot be negative
assert E_actual==E_candidates
assert Eprime_actual=={n for n in Eprime_candidates if n>0}
assert 2*2==2**(0+2)
# (2,4) doubles to (0,0) on Eprime, and dual sends it to (1,0).
sl=(3*2*2+4)//(2*4)
assert sl==2 and sl*sl-2*2==0 and sl*(2-0)-4==0
print('CLASSICAL SAME-E32 RANK ZERO (Tate two-isogeny): squareclasses E={+1,-1}, Eprime={+1,+2}, 2^(r+2)=4 => r=0')
print('SOURCE DEBT: native Kummer squareclass support, both exceptional torsion branches, Tate descent exact sequence remain unproved locally')

print('OPEN: native Kummer/Tate descent receipt, Sha and same-curve analytic native K4, universal S6')
