#!/usr/bin/env python3
"""BR59: original nonlinear moving hypersurface induced metric and K_ab.

For F=n-f(t,x,y,z), tangent frame e_a^mu=δ_a^mu+f_a δ_n^mu,
F_mu=(-f_a,1), z=g^{mu nu}F_mu F_nu>0 and normal n_mu=F_mu/sqrt(z).
The actual second fundamental form is
 K_ab = [e_a^mu e_b^nu (F_{mu nu}-Γ^lambda_{mu nu}F_lambda)]/sqrt(z).
All 10 components of the 4x4 symmetric Israel tensor are retained, as
well as the full nonlinear induced 4x4 metric and chart gradient.

Independent checks: derivation directly by ∇ normal; flat-graph
comparison; arbitrary nonzero ADM shift/warp Christoffel source.
No Ricci/Einstein solution, AdS infinity, trace estimate or existence
is inferred from hypersurface kinematics.

Usage: --part flat|warped|shift
"""
import argparse
import sympy as s
from functools import lru_cache

coords=s.symbols("t x y z n",real=True)
t,x,y,z,n=coords
wall=coords[:4]

def conormal(g, f):
    inv=g.inv()
    Fs=s.Matrix([-s.diff(f,v) for v in wall]+[1])
    z=s.cancel((Fs.T*inv*Fs)[0])
    tangent=s.Matrix(5,4,lambda i,a:
        int(i==a)+(s.diff(f,wall[a]) if i==4 else 0))
    induced=tangent.T*g*tangent
    hess=s.Matrix(5,5,lambda i,j:
        -s.diff(f,coords[i],coords[j]) if i<4 and j<4 else 0)
    return inv,Fs,z,tangent,induced,hess

def christoffel(g, inv, i,j,k):
    return s.cancel(sum(inv[k,r]*(s.diff(g[r,j],coords[i])
          +s.diff(g[r,i],coords[j])-s.diff(g[i,j],coords[r]))/2
                 for r in range(5)))

def direct_K(g,f,point,components=None):
    inv,Fs,norm,T,h,HH=conormal(g,f)
    if s.simplify(point[coords[4]]-f.subs(point))!=0:
        raise ValueError("evaluation point must lie on the actual material graph F=0")
    z=s.simplify(norm.subs(point))
    if z.is_positive is not True:
        raise ValueError("physical spacelike normal requires a positive certificate")
    N=s.sqrt(z)
    result=s.zeros(4)
    required=components if components is not None else [
       (a,b) for a in range(4) for b in range(a,4)]
    for a,b in required:
        # Compute all needed Christoffel contractions at the source point,
        # then physical graph curvature; exact rational inputs encouraged.
        value=s.S.Zero
        for i in range(5):
            for j in range(5):
                weight=s.simplify((T[i,a]*T[j,b]).subs(point))
                if weight==0:continue
                coeff=s.simplify(HH[i,j].subs(point))
                for k in range(5):
                    ff=s.simplify(Fs[k].subs(point))
                    if ff==0:continue
                    coeff-=christoffel(g,inv,i,j,k).subs(point)*ff
                value+=weight*coeff
        result[a,b]=s.simplify(value/N)
        result[b,a]=result[a,b]
    return s.simplify(h.subs(point)),result,z

def flat():
    g=s.diag(-1,1,1,1,1)
    f=(t*x+s.Rational(1,3)*x*y+s.Rational(1,7)*z*z)
    p={t:0,x:0,y:0,z:0,n:0}
    h,K,zz=direct_K(g,f,p)
    assert zz==1
    assert K[0,1]==-1
    assert K[1,2]==-s.Rational(1,3)
    assert K[3,3]==-s.Rational(2,7)
    assert K==K.T
    assert h==s.diag(-1,1,1,1)
    print("BR59 flat nontrivial material graph: 10 original extrinsic/induced components constructed")

def warped():
    # Gaussian AdS-type b(n) with nonzero K at n=0, and f=0.
    b=1+s.Rational(2,5)*n+s.Rational(3,11)*n*n
    g=s.diag(-b*b,b*b,b*b,b*b,1)
    p={t:0,x:0,y:0,z:0,n:0}
    h,K,zz=direct_K(g,s.S.Zero,p)
    assert zz==1 and h==s.diag(-1,1,1,1)
    assert K==s.Rational(2,5)*h
    print("BR59 warped Gaussian: K=(b'/b)h, all 10 original components")

def shift():
    # Shifted physical ADM chart with nonzero normal v^n. The unit
    # normal is NOT the coordinate ∂n. Use flat metric in non-orthogonal
    # coordinates for independent coordinate-invariant source test.
    v=s.Rational(1,3)
    g=s.Matrix([[-1+v*v,0,0,0,v],[0,1,0,0,0],
      [0,0,1,0,0],[0,0,0,1,0],[v,0,0,0,1]])
    p={t:0,x:0,y:0,z:0,n:0}
    h,K,zz=direct_K(g,s.S.Zero,p)
    assert zz==1-v*v
    assert K==s.zeros(4)
    assert h[0,0]==-1+v*v
    print("BR59 shifted ADM: non-unit coordinate normal retained with z=",zz)

if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("--part",choices=["flat","warped","shift"],default="flat")
    arg=ap.parse_args()
    {"flat":flat,"warped":warped,"shift":shift}[arg.part]()
