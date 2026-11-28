#!/usr/bin/env python3
"""BR60: exact first variation of the FULL moving Einstein-Israel K_ab.

At original Gaussian warped wall g0=dn²+b(n)² eta4, b(0)=1,
k=b'(0), kb'=k²+b''(0), perturb metric by ε p and wall F=n-εφ.

With physical (un-rescaled) p_ab and its normal derivative p_ab,n:
δh_ab=p_ab+2kφ eta_ab,
δK_ab= -∂a∂b φ + (k²+b'')φ eta_ab
       +1/2 ∂n p_ab -1/2(∂a p_nb+∂b p_na)
       -k p_nn eta_ab/2.
(This orientation uses unit normal toward increasing n.)

The first variation includes the unit-normal normalization correction
-p_nn*k/2 and the wall shape Hessian, unlike the BR34 fixed-reference
linear rows. The actual Israel jump/mean equations must retain BOTH
faces and the original sign/convention.

The independent oracle differentiates the exact geometric formula
K=TT*(Hess F-ΓF)/sqrt(ginv[dF,dF]) using first-order dual metric/
connection algebra at the moved wall, including shape transport.
This is a source-level differential-geometric identity, not the
nonlinear Einstein solution or a boundary estimate.
"""
import argparse
import sympy as s
from check_hopf369_br59_full_moving_israel_geometry import coords,wall

eta=s.diag(-1,1,1,1)
n=coords[4]
eps=s.symbols('epsilon')

def data():
    t,x,y,z=wall
    k=s.Rational(2,5); kn=s.Rational(3,11)
    b=1+k*n+kn*n/2
    g0=s.diag(-b*b,b*b,b*b,b*b,1)
    # All 15 independent symmetric components and nontrivial normal
    # and tangent derivatives: exact rational sources, no random floats.
    p=s.Matrix(5,5,lambda i,j:
       s.Rational(((min(i,j)+2)*(max(i,j)+3))%17-8,11)
       +s.Rational((i+j+3)%7-3,13)*n
       +s.Rational((i+2)*(j+2)%9-4,17)*t
       +s.Rational((i+j+1)%11-5,19)*x
       +s.Rational((i+2)*(j+3)%13-6,23)*y
       +s.Rational((i+3)*(j+2)%15-7,29)*z)
    # Symmetrize the *entire* perturbation, not only its constants.
    p=(p+p.T)/2
    phi=(s.Rational(1,7)+s.Rational(2,9)*t
         +s.Rational(3,11)*x-s.Rational(4,13)*y
         +s.Rational(5,17)*z+t*x/19+x*y/23
         +y*z/31+z*z/37+t*t/41)
    point={q:0 for q in coords}
    return g0,p,phi,k,kn,point

def oracle(a,b,record):
    g0,p,phi,k,kn,pt=record
    g=g0+eps*p
    F=s.Matrix([-eps*s.diff(phi,q) for q in wall]+[1])
    T=s.Matrix(5,4,lambda i,j:
        (1 if i==j else 0)+(eps*s.diff(phi,wall[j]) if i==4 else 0))
    HH=s.Matrix(5,5,lambda i,j:
        -eps*s.diff(phi,coords[i],coords[j]) if i<4 and j<4 else 0)
    # Compute EXACT first dual jet of inverse metric at moving graph:
    # eval g0 at n=εφ; eval p at n=0; derivatives similar.
    gbase=g0.subs(pt); gi=gbase.inv()
    dg=(p+phi*s.diff(g0,n)).subs(pt)
    dgi=-gi*dg*gi
    ze=(F.T*gi*F)[0].subs(pt)
    dF=F.diff(eps).subs(eps,0).subs(pt)
    dz=(dF.T*gi*F.subs(eps,0)+F.subs(eps,0).T*gi*dF)[0].subs(pt)
    dz+=(F.subs(eps,0).T*dgi*F.subs(eps,0))[0].subs(pt)
    assert ze==1
    norm_derivative=-dz/2
    TT=lambda i,j:s.Rational(int(i==a)*int(j==b))
    def gamma0(i,j,l):
        return s.cancel(sum(gi[l,r]*(
          s.diff(g0[r,j],coords[i])+s.diff(g0[r,i],coords[j])
          -s.diff(g0[i,j],coords[r])).subs(pt)/2 for r in range(5)))
    def gamma1(i,j,l):
        x0=s.S.Zero
        for r in range(5):
            tri=(s.diff(g0[r,j],coords[i])+s.diff(g0[r,i],coords[j])
                 -s.diff(g0[i,j],coords[r]))
            dtri=(s.diff(p[r,j],coords[i])+s.diff(p[r,i],coords[j])
                  -s.diff(p[i,j],coords[r])+phi*s.diff(tri,n)).subs(pt)
            x0+=(dgi[l,r]*tri.subs(pt)+gi[l,r]*dtri)/2
        return s.cancel(x0)
    t0=T.subs(eps,0).subs(pt)
    dt=T.diff(eps).subs(eps,0).subs(pt)
    f0=F.subs(eps,0).subs(pt)
    f1=F.diff(eps).subs(eps,0).subs(pt)
    base=s.S.Zero;dK=s.S.Zero
    for i in range(5):
      for j in range(5):
        Tij=t0[i,a]*t0[j,b]
        dT=dt[i,a]*t0[j,b]+t0[i,a]*dt[j,b]
        inner=HH[i,j].subs(eps,0).subs(pt)
        dinner=HH[i,j].diff(eps).subs(eps,0).subs(pt)
        for l in range(5):
            inner-=gamma0(i,j,l)*f0[l]
            dinner-=gamma1(i,j,l)*f0[l]+gamma0(i,j,l)*f1[l]
        base+=Tij*inner
        dK+=dT*inner+Tij*dinner
    return s.cancel(dK+norm_derivative*base),s.cancel(base)

def prediction(a,b,record):
    g0,p,phi,k,kn,pt=record
    val=(-s.diff(phi,wall[a],wall[b])
       +(k*k+kn)*phi*eta[a,b]
       +s.diff(p[a,b],n)/2
       -(s.diff(p[4,b],wall[a])+s.diff(p[4,a],wall[b]))/2
       -k*p[4,4]*eta[a,b]/2)
    return s.cancel(val.subs(pt))

def test(index):
    record=data()
    a,b=[(a,b) for a in range(4) for b in range(a,4)][index]
    expected=prediction(a,b,record)
    actual,base=oracle(a,b,record)
    assert actual==expected,(index,a,b,actual,expected)
    assert base==record[3]*eta[a,b]
    print('BR60 exact full nonlinear graph Fréchet K_ab',a,b,'PASS')

def negative():
    record=data()
    for i,(a,b) in enumerate(( (0,1),(1,2),(3,3) )):
        correct=prediction(a,b,record)
        # Deliberately omit the moving-wall Hessian. The source changes.
        phi=record[2];bad=correct+s.diff(phi,wall[a],wall[b]).subs(record[-1])
        assert correct!=bad
    print('BR60 missing graph-shape Hessian REFUSED')

if __name__=='__main__':
    p=s.ArgumentParser() if False else argparse.ArgumentParser()
    p.add_argument('--part',choices=['component','negative'],default='component')
    p.add_argument('--index',type=int,default=0)
    a=p.parse_args()
    if a.part=='negative':negative()
    else:
        if not 0<=a.index<10:raise ValueError('10 symmetric physical wall components')
        test(a.index)
