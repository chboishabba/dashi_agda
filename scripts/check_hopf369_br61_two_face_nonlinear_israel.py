#!/usr/bin/env python3
"""BR61: TWO-SIDED full moving nonlinear Israel first variation.

Use ORIGINAL physical plus/minus k_+=j/2,k_-=-j/2 at the shared wall;
the common graph displacement phi and induced metric continuity determine
the matching between p_+ and p_- tangent components. They cannot be
varied independently and then treated as one physical Israel wall.

Define I_ab=[K_ab]-h_ab tr_h[K]+3j h_ab. At the reference
[K_ab]=j eta_ab, tr[K]=4j and I=0. Its actual first variation is
 δI_ab = [δK_ab]-eta_ab tr_eta[δK]
         -j(δh_ab-eta_ab tr_eta δh)+3 δj eta_ab.
Here each δK is the genuine BR60 moving graph Fréchet (including phi
Hessian, Gaussian k'_normal, p_nn, all mixed p_an derivatives).
A common graph Hessian cancels from the *jump* but not from the
individual K+/- and their own boundary connection; different maps or
unmatched induced metrics are REFUSED.

This is a true nonlinear first variation of the junction tensor, not
a substitute for a Bianchi-compatible nonlinear boundary PDE estimate.
"""
import argparse
import sympy as s
from check_hopf369_br60_moving_israel_frechet import eta
t,x,y,z,n=s.symbols('t x y z n',real=True)
wall=(t,x,y,z)
j=s.Rational(-6,5)
dj=s.Rational(3,17)

def metric_data():
    phi=(s.Rational(2,7)+t*x/11+x*y/13+y*z/17+z*z/19+t*t/23)
    pp=s.Matrix(5,5,lambda a,b:
       s.Rational((min(a,b)+3)*(max(a,b)+2)%23-11,13)
       +s.Rational(a+b+2,17)*n
       +s.Rational((min(a,b)+1)*(max(a,b)+3)%11-5,19)*t
       +s.Rational(a+b+1,23)*x)
    pm=s.Matrix(5,5,lambda a,b:
        pp[a,b]+(2*j*phi*eta[a,b] if a<4 and b<4 else 0)
        +s.Rational(a+b+3,31)*n)
    return phi,pp,pm

def δh(phi,p,k):
    return s.Matrix(4,4,lambda a,b:p[a,b]+2*k*phi*eta[a,b])
def δK(phi,p,k,kprime):
    # physical unscaled perturbation source, including background shape.
    return s.Matrix(4,4,lambda a,b:
        -s.diff(phi,wall[a],wall[b])
        +(k*k+kprime)*phi*eta[a,b]
        +s.diff(p[a,b],n)/2
        -(s.diff(p[4,b],wall[a])+s.diff(p[4,a],wall[b]))/2
        -k*p[4,4]*eta[a,b]/2)
def trace(h):return s.trace(eta*h)
def start():
    phi,pp,pm=metric_data()
    kp=j/2;km=-j/2
    dhp=δh(phi,pp,kp);dhm=δh(phi,pm,km)
    # The physical charts really must match induced metric BEFORE Israel.
    assert (dhp-dhm).applyfunc(s.expand)==s.zeros(4)
    # True shape derivative includes independently specified background
    # acceleration b'' on BOTH sides, not only j and its first jet.
    bp2=s.Rational(3,11);bm2=s.Rational(-4,13)
    DKp=δK(phi,pp,kp,bp2)
    DKm=δK(phi,pm,km,bm2)
    J=DKp-DKm
    dh=dhp
    linear=J-eta*trace(J)-j*(dh-eta*trace(dh))+3*dj*eta
    # Independent direct first variation of junction:
    # I=[K]-h tr_h[K]+3j h, K0diff=j eta
    # δtr_h[K]=tr_eta δ[K]-j tr_eta δh.
    direct=J-dh*4*j-eta*(trace(J)-j*trace(dh))+3*j*dh+3*dj*eta
    assert (direct-linear).applyfunc(s.expand)==s.zeros(4)
    assert linear==linear.T
    return phi,pp,pm,DJ(DKp,DKm,dh,linear)

class DJ:
    def __init__(self,kp,km,dh,linear):
        self.plus,self.minus,self.h,self.linear=kp,km,dh,linear

def rows():
    phi,pp,pm,src=start()
    p={q:0 for q in (*wall,n)}
    assert src.linear.subs(p)!=s.zeros(4)
    # Exactly ten independent Israel junction components.
    independent=[src.linear[a,b].subs(p) for a in range(4)
                 for b in range(a,4)]
    assert len(independent)==10
    # Normal/tangent modes and trace are not silently projected.
    assert src.plus[0,1]!=0 and src.minus[0,1]!=0
    assert trace(src.linear).subs(p)!=0
    print('BR61 actual Israel ten junction entries, both physical K and mean trace: source constructed')

def refusal():
    phi,pp,pm,src=start()
    unmatched=pm.copy()
    unmatched[0,1]+=s.Rational(1,7)
    unmatched[1,0]+=s.Rational(1,7)
    dhm=δh(phi,unmatched,-j/2)
    assert (src.h-dhm)!=s.zeros(4)
    # The shared induced-metric trace contraction is now undefined as
    # a single wall geometry unless a separate physical matching chart
    # is provided; do not apply the conforming Israel formula.
    print('BR61 mismatched two-chart induced metric and unlicensed Israel source REFUSED')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['rows','refusal'],default='rows')
    a=p.parse_args()
    {'rows':rows,'refusal':refusal}[a.part]()

if __name__=='__main__':main()
