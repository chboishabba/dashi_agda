#!/usr/bin/env python3
"""Original Caldwell–Langlois (2001) source Eq(1),(4),(17)-(20), AdS5.

Caldwell & Langlois, "Shortcuts in the fifth dimension", Phys Lett B
511:129-135, DOI 10.1016/S0370-2693(01)00631-1,
original arXiv gr-qc/0103070, original Eq.(19) PDF page 5.
The source model uses flat k=0, mass mu=0, AdS ell=1:
 ds5²=-R² dT² + dR²/R² + R² (dr²+du²+dv²), Lambda5=-6.
Choose Z2-tuned brane tension sigma=1, kappa5²=6,
brane a(t)=t, H=1/t, rho=sqrt(1+t^-2)-1, and conservation p.
These satisfy the original modified FRW/Friedmann equation, brane
proper-time normalization, and NEC rho+p>0.

Source gravitational-horizon expression Eq19:
 rg² = [int_A^B(dt/a)*sqrt(1+ell²H²)]²
        -[int_A^B(dt/a)*ell*H]².
 Photon radius Eq20: r_gamma=int_A^B dt/a.
Use tA=1 and tB=2; exact definite integrals I1,I2, numerical
evaluation; solve SAME RECEIVER proper arrival t_gamma=exp(rg)>2;
build explicit 5D geodesic from source Eq17 and check null and
non-affine geodesic. Check all 25 5D Einstein+Lambda components.
Original physical AdS bulk is NOT the prior flat cylindrical test brane.

Important: not independently checking distributional Israel junction
or perturbative stability, quantum graviton/brane couplings,
physical energy-budget apparatus, GW170817 differential delay or
experiment. This is a dimensionless exact classical SOURCE MODEL.
"""
import sympy as s
import mpmath as mp
import json

def audit():
    t=s.symbols("t",positive=True,real=True)
    a=t;H=1/t
    ell=s.Integer(1);kappa5sq=s.Integer(6);sigma=s.Integer(1)
    lam5=-6
    rho=s.sqrt(1+t**-2)-1
    pressure=s.simplify(-rho-s.diff(rho,t)/(3*H))
    friedmann=(kappa5sq**2/s.Integer(36))*(rho+sigma)**2+lam5/s.Integer(6)
    assert s.simplify(H*H-friedmann)==0
    assert s.simplify(s.diff(rho,t)+3*H*(rho+pressure))==0
    assert s.simplify(rho+pressure-1/(3*t**2*s.sqrt(1+t**-2)))==0
    assert s.simplify(kappa5sq**2*sigma**2+6*lam5)==0
    dTdt=s.sqrt(1+t*t)/t**2
    assert s.simplify(-t*t*dTdt*dTdt+1/t**2+1)==0

    # Source original Eq(18),(19),(20), not an arbitrary path metric.
    I1primitive=s.asinh(t)-s.sqrt(1+t*t)/t
    assert s.simplify(s.diff(I1primitive,t)-s.sqrt(1+t*t)/t**2)==0
    I1=s.simplify(I1primitive.subs(t,2)-I1primitive.subs(t,1))
    I2=s.Rational(1,2)
    rg=s.sqrt(I1*I1-I2*I2)
    rph=s.log(2)
    rgN=mp.mpf(str(s.N(rg,60)))
    rphN=mp.log(2)
    assert rgN>rphN
    tPhoton=mp.exp(rgN)
    assert tPhoton>2

    # Original Eq17: (1/RA-1/RB)²+r²/ell²=(TB-TA)²/ell^4
    # Recover explicit bulk null geodesic with 5D T as parameter:
    # d(1/R)/dT=-alpha, dr/dT=P/E (Eq12,15,16).
    T,R,r,u,v=s.symbols("T R r u v",positive=True,real=True)
    alpha=s.simplify(I2/I1)
    PoverE=s.simplify(rg/I1)
    assert s.simplify(alpha*alpha+PoverE*PoverE-1)==0
    RofT=1/(1-alpha*T)
    rofT=PoverE*T
    assert s.simplify(RofT.subs(T,0)-1)==0
    assert s.simplify(RofT.subs(T,I1)-2)==0
    assert s.simplify(rofT.subs(T,I1)-rg)==0
    dR=s.diff(RofT,T);dr=s.diff(rofT,T)
    assert s.simplify(-RofT**2+dR**2/RofT**2+RofT**2*dr**2)==0

    # Verify the actual 3-coordinate bulk null ray solves its geodesic
    # equation (T need not be an affine geodesic parameter).
    g3=s.diag(-R**2,R**-2,R**2)
    inverse3=s.diag(-R**-2,R**2,R**-2)
    cs3=(T,R,r)
    G3={}
    for k in range(3):
      for i in range(3):
        for j in range(3):
          G3[k,i,j]=s.simplify(s.Rational(1,2)*sum(
            inverse3[k,h]*(s.diff(g3[h,j],cs3[i])+s.diff(g3[h,i],cs3[j])-s.diff(g3[i,j],cs3[h]))
            for h in range(3)))
    velocity=s.Matrix([1,dR,dr])
    acc=s.Matrix([sum(G3[k,i,j].subs(R,RofT)*velocity[i]*velocity[j]
                         for i in range(3) for j in range(3))
                  +s.diff(velocity[k],T) for k in range(3)]).applyfunc(s.simplify)
    nonaffine=acc[0]
    assert all(s.simplify(acc[k]-nonaffine*velocity[k])==0 for k in range(3))

    # Independently verify full AdS5 original 5D Einstein tensor:
    # Ric_AB = -4 g_AB, Ric=-20, G_AB=6 g_AB and Lambda=-6.
    cs=(T,R,r,u,v)
    g5=s.diag(-R**2,R**-2,R**2,R**2,R**2)
    gi=s.diag(-R**-2,R**2,R**-2,R**-2,R**-2)
    Gamma={}
    for k in range(5):
      for i in range(5):
        for j in range(5):
          Gamma[k,i,j]=s.simplify(s.Rational(1,2)*sum(
            gi[k,h]*(s.diff(g5[h,j],cs[i])+s.diff(g5[h,i],cs[j])-s.diff(g5[i,j],cs[h]))
            for h in range(5)))
    Ric=s.Matrix(5,5,lambda i,j:s.simplify(sum(
      s.diff(Gamma[h,i,j],cs[h])-s.diff(Gamma[h,h,j],cs[i])
      +sum(Gamma[h,h,m]*Gamma[m,i,j]-Gamma[h,i,m]*Gamma[m,h,j]
           for m in range(5)) for h in range(5))))
    assert all(s.simplify(Ric[i,j]+4*g5[i,j])==0 for i in range(5) for j in range(5))
    scal=s.simplify(sum(gi[i,i]*Ric[i,i] for i in range(5)))
    assert scal==-20
    Einstein=(Ric-scal*g5/2).applyfunc(s.simplify)
    assert all(s.simplify(Einstein[i,j]+lam5*g5[i,j])==0 for i in range(5) for j in range(5))
    return {
      "status":"PASS original source Eq19 AdS5/FRW same-receiver shortcut, mathematical only",
      "original_paper_DOI":"10.1016/S0370-2693(01)00631-1",
      "original_arxiv":"gr-qc/0103070",
      "bulk_original_source_f_R":"R²/ell², k=mu=0, ell=1",
      "bulk_Einstein_Lambda_all_25":True,"bulk_Ricci_scalar":str(scal),
      "negative_bulk_Lambda":-6,"source_kappa5_sq":str(kappa5sq),
      "brane_tension":str(sigma),"brane_FRW":"a(t)=t, H=1/t",
      "brane_rho":str(rho),"brane_pressure":str(pressure),
      "original_Friedmann_and_continuity":True,
      "brane_rho_plus_pressure_positive":True,
      "original_bulk_null_and_geodesic":True,
      "same_receiver_comoving_r":float(rgN),
      "photon_horizon_at_t2":float(rphN),
      "bulk_horizon_at_t2":float(rgN),
      "bulk_receipt_brane_proper_t":2.0,
      "same_receiver_photon_proper_t":float(tPhoton),
      "same_receiver_bulk_time_advantage":float(tPhoton-2),
      "source_I1_exact":str(I1),"source_I2_exact":str(I2),
      "all_Israel_distributional_conditions_independently_accepted":False,
      "all_mode_stability":False,"bulk_graviton_emission_detection":False,
      "GW170817_delay_constraint_modelled":False,
      "FTL_in_full5D_or_CTC":False
    }

if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
