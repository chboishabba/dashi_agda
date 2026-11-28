#!/usr/bin/env python3
"""BR66: nonzero-MEAN original BR34 optical vs full moving Israel source.

The frozen BR34 reference uses k_ref^+=j/2, k_ref^-=-j/2.
The actual geometric two-face background can have
  k_+=m+j/2, k_-=m-j/2, m not assumed zero.

Raw coordinate normal metric perturbations include 2k± H± and
reference optical normal derivatives remain px±; hence actual
linear extrinsic K± = K_BR34± + m H± + shape±.
Shape± = -Hess(phi)+(k±²+b±'') phi eta.

Physical induced matching requires H_- = H_+ +2j phi eta.
The true geometric 10-row R=2[delta K]-2j delta h then satisfies
  R-J_BR34 = 2{b_+''-b_-''-2 m j} phi eta,
with NO division by tangent frequency. This is nonzero in general
even when b+''=b-'' if m j phi !=0.

This source corrects claims that full nonzero-mean nonlinear wall
geometry is automatically covered by the mean-free BR34 operator.
"""
import sympy as s
import argparse
from check_hopf369_br_warped_physical_attachment import E4,metric_side,metric_rows,keys,trace4

def tensor(H,b,l):
    return H.row_join(b).col_join(b.T.row_join(s.Matrix([[2*l]])))

def run():
    mean,j,phi,bpp,bmp,dj=s.symbols("mean j phi bpp bmp dj",real=True)
    kp=mean+j/2;km=mean-j/2
    q=s.Matrix(s.symbols("q0:4"))
    H=s.Matrix(4,4,lambda a,b:s.Symbol("H%d%d"%(min(a,b),max(a,b))))
    Hm=H+2*j*phi*E4
    beta=s.Matrix(s.symbols("bp0:4"))
    betam=s.Matrix(s.symbols("bm0:4"))
    lp,lm=s.symbols("lp lm")
    xp=s.Matrix(4,4,lambda a,b:s.Symbol("xp%d%d"%(min(a,b),max(a,b))))
    xm=s.Matrix(4,4,lambda a,b:s.Symbol("xm%d%d"%(min(a,b),max(a,b))))
    pp=tensor(H,beta,lp);pm=tensor(Hm,betam,lm)
    px=tensor(xp,s.zeros(4,1),0);mx=tensor(xm,s.zeros(4,1),0)
    Kp=metric_side(pp,px,q,j/2)[2]
    Km=metric_side(pm,mx,q,-j/2)[2]
    J=2*(Kp-Km)-j*(H+Hm)
    actualKp=Kp+mean*H+(kp**2+bpp)*phi*E4
    actualKm=Km+mean*Hm+(km**2+bmp)*phi*E4
    # Shared graph Hessian cancels in the jump, but the individual
    # K± contain it; its differentiated source remains at each face.
    common=H+2*kp*phi*E4
    assert (common-Hm-2*km*phi*E4).applyfunc(s.expand)==s.zeros(4)
    R=2*(actualKp-actualKm)-2*j*common
    correction=2*(bpp-bmp-2*mean*j)*phi*E4
    assert (R-J-correction).applyfunc(s.expand)==s.zeros(4)
    # Independent original BR34 D/E reference rows, 10 Israel entries.
    for a in "DE":
        rows=metric_rows(pp,px,pm,mx,q,j,a)
        assert (rows[14:24,0]-s.Matrix([J[i,k] for i,k in keys])).applyfunc(s.expand)==s.zeros(10)
    # BR64 bidirectional trace reverse applies to corrected geometric R.
    I=(R-E4*trace4(R))/2+3*dj*E4
    back=2*(I-3*dj*E4-E4*trace4(I-3*dj*E4)/3)
    assert (back-R).applyfunc(s.expand)==s.zeros(4)
    assert correction.subs({bpp:0,bmp:0,mean:0})==s.zeros(4)
    assert correction.subs({bpp:0,bmp:0,mean:1,j:1,phi:1})==-4*E4
    assert correction.subs({bpp:1,bmp:0,mean:0,j:1,phi:1})==2*E4
    print("PASS BR66 actual two-face mean/jump/collar nonlinear Israel source identity")
    print("PASS BR66 reference D/E 10+10, BIDI trace and independent nonzero-mean refusal")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.parse_args()
    run()
