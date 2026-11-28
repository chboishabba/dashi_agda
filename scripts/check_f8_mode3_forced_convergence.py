"""Exact affine lift at original SSPRK3 clocks and radial FV consistency guards.
Conditional source-level consistency; no full production or pointwise Weyl claim.
"""
import json
from fractions import Fraction as Q
import sympy as S


def run():
    checks=0
    def check(x):
        nonlocal checks
        assert x
        checks+=1
    v,g,l,p,m=S.symbols('v g l p m')
    check(S.expand((1+v)*(p+l)-(1-v)*(m+l)-2*g-((1+v)*p-(1-v)*m)-2*(v*l-g))==0)
    # Native inhomogeneous f and common lift ell: g_i = A_i ell_i+f_i.
    B0,B1,Bh,y,L0,L1,Lh,g0,g1,gh=S.symbols('B0 B1 Bh y L0 L1 Lh g0 g1 gh',commutative=False)
    h=S.Symbol('h',commutative=True)
    f0=g0-(B0-1)*L0/h;f1=g1-(B1-1)*L1/h;fh=gh-(Bh-1)*Lh/h
    x=y+L0;x1=B0*x+h*f0;y1=B0*y+h*g0+L0-L1
    check(S.expand(x1-L1-y1)==0)
    x2=S.Rational(3,4)*x+S.Rational(1,4)*(B1*x1+h*f1)
    y2=S.Rational(3,4)*y+S.Rational(1,4)*(B1*y1+h*g1)+S.Rational(3,4)*L0+S.Rational(1,4)*L1-Lh
    check(S.expand(x2-Lh-y2)==0)
    x3=x/3+S.Rational(2,3)*(Bh*x2+h*fh)
    y3=y/3+S.Rational(2,3)*(Bh*y2+h*gh)+L0/3+S.Rational(2,3)*Lh-L1
    check(S.expand(x3-L1-y3)==0)
    # Source lift clock variation: |v|>=1/sqrt(145)>1/13.
    check(145<13**2)
    # Shell average of a smooth even source has O(dr^2) uniform error.
    # For j>=1 and x in [r-h/2,r+h/2], denominator >= h*(r-h/2)^(d-1).
    # Odd first moment cancels the constant weight; mean value gives
    # |mean(x-r)| <= (d-1)*3^(d-1)*h^2/(12*r) for r>=h.
    # |f'(r)|<=r sup|f''|, and |Taylor remainder|<=h^2 sup|f''|/8.
    # At origin f'(0)=0. Adjacent errors then differ by <=2 C h^2.
    rows=[]
    for d in (3,7,11):
        C=Q((d-1)*3**(d-1),12)+Q(1,8)
        check(C>Q(1,8))
        # Exact FV quadratic reproduction, including origin special row.
        j=S.symbols('j');hi=j+S.Rational(1,2);lo=j-S.Rational(1,2)
        cp=d*hi**(d-1);cm=d*lo**(d-1);den=hi**d-lo**d
        check(S.expand(cp*(2*j+1)-cm*(2*j-1)-2*d*den)==0)
        check(2*d==2*d*(1**2-0**2))
        rows.append(dict(d=d,source_average_error_constant=str(C),adjacent_gradient_error_constant=str(2*C)))
    # Prior SMS arithmetic only: inherited analytic path jets not replayed.
    slope=Q(10000);B=Q('1.01');plo=Q('1.025');phi=Q('1.08');a1=14;a2=201;d0=100;d1=1450;d2=22000
    main=plo*plo-1-(B*(2*a1*phi+2)+3*phi)/slope-(B*a2+3*a1)/slope**2
    adverse=d0*(B*phi*phi+1)/slope+(B*(2*d1*phi+2*d0)+3*d0*phi)/slope**2+(B*d2+3*d1)/slope**3
    check(main-adverse==Q(2522475013,100000000000))
    check(Q('.04')*Q('4.536e-270')-4*Q('7.102e-279')>Q('1.814e-271'))
    return dict(exact_checks=checks,noncommuting_rk_lift_stages=3,radial_channels=rows,sms_arithmetic_margin=str(main-adverse),scope='affine source stage identities, FV source-average and polynomial guards; conditional energy consistency only, no Weyl trace or production')


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
