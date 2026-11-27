#!/usr/bin/env python3
"""Exact real-ray first-coefficient reduction; not a proof of the analytic germ."""
import sympy as s
from fractions import Fraction as F

A,B,S2,S3,P2,P3,k,p,a,b,w=s.symbols('A B S2 S3 P2 P3 k p a b w')
c=s.Rational(163,41)
m=s.Rational(163,1681)
N0=A*A; M0=c*A*A
N1=-s.Rational(81,41)*A*B; M1=m*A*B
R=((N1*P2+N0*P3*A)-(M1*S2+M0*S3*A))*A*A+(N0*P2-M0*S2)*2*A*B-N0*M0*A*S3
normalized=R.subs({P2:c*S2,P3:2*c*S3+c*k*S2})
assert s.expand(normalized-c*A**3*S2*(k*A*A-2*B))==0
assert s.expand(41*R-A**3*((41*P3-326*S3)*A*A-326*B*S2)-A**3*B*(41*P2-163*S2)/41)==0
assert s.expand((k*A*A-2*B).subs({A:-2*p*a,B:-2*p*a+2*p*p*b})-4*p*(p*k*a*a-(p*b-a)))==0
u=-2*p*w/(1-w)
assert s.expand(s.series(a*u+b*u*u/2,w,0,3).removeO()-(-2*p*a*w+(-2*p*a+2*p*p*b)*w*w))==0
alpha,beta=s.symbols('alpha beta')
g=s.groebner([alpha*beta-1,41*(alpha+beta)+81],alpha,beta,domain=s.QQ)
for expr in [alpha*beta-1,(1-alpha)*(1-beta)-c,alpha*beta**2+beta*alpha**2+s.Rational(81,41),(1-alpha**2)*(1-beta)+(1-alpha)*(1-beta**2)-m]:
    assert g.reduce(expr)[1]==0
# Nonzero signed orientations, actual kappa, reverse-solved b, and perturbations.
kv=F(-77859659565707,19943834790540897829879824384000)
count=0
for pv in [F(1,3),F(2),F(41,3)]:
    for av in [-7,-1,1,7]:
        for sv in [-13,-1,1,13]:
            for tv in [-9,0,9]:
                bv=kv*av*av+F(av,pv)
                A0=-2*pv*av; B0=-2*pv*av+2*pv*pv*bv
                def val(B0):
                    return c*A0**3*sv*(kv*A0*A0-2*B0)
                assert val(B0)==0
                assert val(B0+2*pv*pv)!=0
                count+=1
# Degenerate zero modes must not be promoted to a derivative certificate.
assert normalized.subs(A,0)==0 and normalized.subs(S2,0)==0
print(f'SymPy {s.__version__}: 8 symbolic identities, {count} signed reverse-solved cases, {count} perturbed cases, 2 degenerate controls PASS')
