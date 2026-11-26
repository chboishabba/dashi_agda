"""Causal-cap source moment sign and anchored fourth-derivative budget.
Conditional on the existing continuum support and C4 dual on the cap.
No propagation, dual jet or continuum sign enclosure is asserted.
"""
from fractions import Fraction as Q
from math import prod,ceil
import json
import sympy as S

EPS=Q(1,25);U0=1-Q(361,10**6)/EPS;X0=U0*U0
POLYS=((6,81,-92,-46,70,-15),(6,54,-109,58,-7),(24,-36,12,1))
SCALES=(Q(8,5),Q(32,7),Q(16,35));UNIT=10**150


def upper(x):
    assert x>=0
    return Q(ceil(x*UNIT),UNIT)


def poly_box(p,a,b):
    lo=hi=Q(p[0]);a=a*a;b=b*b
    for c in p[1:]:
        w=(lo*a,lo*b,hi*a,hi*b);lo=min(w)+c;hi=max(w)+c
    return lo,hi


def run():
    y=S.symbols('y');checks=0;rows=[]
    for i,d in enumerate((3,7,11)):
        p=POLYS[i];shift=S.Poly(sum(c*(1-y)**(len(p)-j-1) for j,c in enumerate(p)),y)
        a=[Q(shift.nth(j)) for j in range(shift.degree()+1)]
        # y=1-u^2, 0<=y<=1-X0. Discard positive nonconstant terms.
        lower=a[0]+sum(c*(1-X0)**j for j,c in enumerate(a) if c<0)
        assert lower>0;checks+=1
        # y2=1/(1-u^2)>8, so y2^8 exp(1-y2) decreases.
        mass=Q(0);c4=Q(0)
        for j in range(64):
            u=U0+(1-U0)*j/64;v=U0+(1-U0)*(j+1)/64
            z=min(Q(256),1/(1-u*u));assert z>8
            t=Q(1);den=t
            for k in range(1,129):t*= (z-1)/k;den+=t
            lo,hi=poly_box(p,u,v)
            ub=SCALES[i]*max(abs(lo),abs(hi))*z**8/den
            w=EPS**d*(v**d-u**d)/d*ub
            mass+=upper(w);c4+=upper(w*(v*v-X0)**4/24)
        assert mass>0 and c4>0
        rows.append(dict(d=d,profile_polynomial_lower=str(lower),mass_upper=str(mass),anchored_M4_coefficient_upper=str(c4),mass_display=float(mass),M4_display=float(c4)))
    print(json.dumps(dict(scope='conditional cap support and C4 continuum dual; rigorous source-only coefficients and positive source profile on cap, not sign of dual',u0=str(U0),x0=str(X0),exact_profile_sign_checks=checks,tiles=64,rows=rows),indent=2))

if __name__=='__main__':run()
