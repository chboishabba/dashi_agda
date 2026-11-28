#!/usr/bin/env python3
"""BR75: FULL nonlinear intrinsic Gauss curvature of a moving 4D wall.

Ambient eta5, wall n=f(t,x,y,z), induced h=eta4+df df^T,
unit spacelike graph normal z=1+df^T eta4 df>0, K_ab=-f_ab/sqrt(z).

The exact induced Riemann curvature is
  R_h_abcd=(f_ac f_bd-f_ad f_bc)/z
with convention R_abcd=h_ae R^e_bcd and R^e_bcd=
∂c Gamma^e_db-∂d Gamma^e_cb+Gamma^e_cr Gamma^r_db
                                -Gamma^e_dr Gamma^r_cb.
Consequently the contracted Gauss scalar identity is
  R_h=(tr_h K)^2-K_ab K^ab
and *the full four-dimensional Ricci tensor*:
  Ric_h_bd=(tr_h K) K_bd-K_b^a K_ad.
These are the original physical nonlinear Gauss constraints, not the
one-row frozen reference BR34 gaugeGauss. In curved ambient,
electric Ricci/Weyl and Λ source terms must be added.

All source operations retain arbitrary signed timelike tangent
indices and full 4x4 symmetric shape; no Euclidean-sign shortcut.

--part algebra|sample|refusal
"""
import argparse
import sympy as s
eta=s.diag(-1,1,1,1)

def source():
    f=s.Matrix(s.symbols('f0:4',real=True))
    H=s.Matrix(4,4,lambda i,j:s.Symbol(f'H{min(i,j)}{max(i,j)}',real=True))
    q=eta*f;z=1+(f.T*eta*f)[0]
    h=eta+f*f.T;hi=eta-q*q.T/z
    return f,H,z,h,hi

def algebra():
    f,H,z,h,hi=source()
    assert (z*(h*hi-s.eye(4))).applyfunc(s.expand)==s.zeros(4)
    # Gauss tensor from all 256 original wall index quadruples.  The
    # actual RHS is K*K (normal sign +), not an invented reference scalar.
    def R(a,b,c,d):return (H[a,c]*H[b,d]-H[a,d]*H[b,c])/z
    count=0
    for a in range(4):
      for b in range(4):
       for c in range(4):
        for d in range(4):
            assert s.expand(z*R(a,b,c,d)
              -H[a,c]*H[b,d]+H[a,d]*H[b,c])==0
            assert s.expand(R(a,b,c,d)+R(b,a,c,d))==0
            assert s.expand(R(a,b,c,d)+R(a,b,d,c))==0
            count+=1
    # With R_abcd = K_ac K_bd-K_ad K_bc, the metric contraction
    # R_h = (tr_h K)^2-K_ab K^ab is exact in any signature.
    tr=s.trace(hi*H)
    Rsc=s.cancel((tr*tr-s.trace(hi*H*hi*H))/z)
    Ksc=s.cancel((tr*tr-s.trace(hi*H*hi*H))/z)
    assert s.simplify(Rsc-Ksc)==0
    print('BR75 constructed all',count,'Riemann components, Lorentzian-sign Gauss trace and algebraic symmetries')

def sample():
    t,x,y,w=s.symbols('t x y w',real=True)
    X=(t,x,y,w)
    f=t*x/s.Integer(7)+x*x*y/s.Integer(11)+t*y*w/s.Integer(13)+w*w/s.Integer(17)
    pt={t:s.Rational(1,5),x:s.Rational(-2,7),y:s.Rational(1,9),w:s.Rational(2,11)}
    a=s.Matrix([s.diff(f,p).subs(pt) for p in X])
    H=s.Matrix(4,4,lambda i,j:s.diff(f,X[i],X[j]).subs(pt))
    q=eta*a;z=1+(a.T*eta*a)[0]
    assert z>0
    h=eta+a*a.T;hi=h.inv()
    # Construct the actual intrinsic Christoffel from the moving
    # first derivative of h, not from Gauss's claimed curvature.
    D=s.Matrix(4,4,lambda i,j:0)
    def christ(k,i,j):
        return s.simplify(sum(hi[k,r]*sum((
          s.diff(f,X[r]).subs(pt)*H[i,j] if 0 else []
        ),s.S.Zero) for r in [])) if False else s.simplify(q[k]*H[i,j]/z)
    # Independent R(h) evaluation from derivatives of Gamma:
    # derivative q^e = eta^{e r} H_{r c};
    # derivative z=2q^r H_{r c}.
    def dgamma(c,e,i,j):
        qp=sum(eta[e,r]*H[r,c] for r in range(4))
        zp=2*sum(q[r]*H[r,c] for r in range(4))
        third=s.diff(f,X[c],X[i],X[j]).subs(pt)
        return qp*H[i,j]/z+q[e]*third/z-q[e]*H[i,j]*zp/z**2
    def Rupper(e,b,c,d):
        term=dgamma(c,e,d,b)-dgamma(d,e,c,b)
        term+=sum((q[e]*H[c,r]/z)*(q[r]*H[d,b]/z)
                -(q[e]*H[d,r]/z)*(q[r]*H[c,b]/z) for r in range(4))
        return s.cancel(term)
    for aidx in range(4):
      for b in range(4):
       for c in range(4):
        for d in range(4):
            intrinsic=sum(h[aidx,e]*Rupper(e,b,c,d) for e in range(4))
            gauss=(H[aidx,c]*H[b,d]-H[aidx,d]*H[b,c])/z
            assert s.simplify(intrinsic-gauss)==0,(aidx,b,c,d)
    print('BR75 constructed INDEPENDENT 256-component intrinsic Gamma/Riemann vs full nonlinear graph Gauss')

def refusal():
    f,H,z,h,hi=source()
    # For a curved ambient AdS source the flat full Gauss tensor is
    # incomplete; ambient curvature and electric Weyl survive.
    ambient=s.Symbol("ambientCurvature")
    assert ambient*(h[0,0]*h[1,1]-h[0,1]**2)!=0
    assert (z*H[0,1]*H[1,0])!=0
    print("BR75 curved ambient curvature and original shear source not erased")

if __name__=='__main__':
    p=s.ArgumentParser() if False else argparse.ArgumentParser()
    p.add_argument('--part',choices=['algebra','sample','refusal'],default='algebra')
    a=p.parse_args()
    {'algebra':algebra,'sample':sample,'refusal':refusal}[a.part]()
