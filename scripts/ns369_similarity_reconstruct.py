#!/usr/bin/env python3
"""Independent NS similarity candidate reconstruction (NOT a proof certificate).

Original equation and harmonic lattice: L. Alpoge and T. Buckmaster,
Finite-time blow-up for the Navier-Stokes equations, 20 Nov 2026,
https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546
lean/Challenge.lean; lean/Breakdown/CertCell/StatementDefs.lean; Appendix C.
DASHI extension: smooth rational potential basis, full signed Fourier
collocation, forced-to-unforced homotopy, numerical cell/adjoint diagnostics.
No claim to reproduce the authors' unpublished spline coefficients.
Requires numpy, scipy, sympy. Run from repository root.
"""
import argparse
import json
import time
from pathlib import Path
from itertools import product
import numpy as np
import sympy as S
from scipy.optimize import least_squares
from ns_cell_signed_node import source_label, source_inverse, source_flip

FIELDS = ("cell","shape_valueSets","entry_conditions","enclosure_numbers",
          "coerciveL2_ge","coercivePin_ge","certificate","instantiation",
          "offset_expansion","shift_numbers","frozen_form","adjoint_quadratic",
          "adjoint_links","potential_entries","adjoint_defect")
x,y,z=S.symbols("x y z", real=True)
xyz=(x,y,z)
D=1+x*x+y*y+z*z
I=S.I
Y=S.Matrix(xyz)


def curl(v):
    return S.Matrix([S.diff(v[2],y)-S.diff(v[1],z),
                     S.diff(v[0],z)-S.diff(v[2],x),
                     S.diff(v[1],x)-S.diff(v[0],y)])


def scalar(a,k,j,odd):
    """Cartesian smoothness at axis and origin; critical tail.
    j increases radial approximation order without degrading decay.
    Odd potential under flip (x,-y,-z) compensates e_z flip.
    """
    n=abs(a)*19
    p=(x+I*y)**n if a>=0 else (x-I*y)**n
    if odd:
        p=p*z if a==0 else p
    power=S.Rational(n+(1 if odd and a==0 else 0)-k,2)
    return p*D**(-power-j)  # k=0 toroidal potential; k=1 poloidal


def build_basis(level,omega):
    """Reflection and conjugation orbits; no modulo reduction of true labels.
    Each real basis coefficient multiplies a complete orbit.
    Independent real/imag amplitudes except self-conjugate orbits.
    """
    ez=S.Matrix([0,0,1]); out=[]
    for a in range(level+1):
        for k in range(-level,level+1):
            if (k+a)%2 or (a==0 and k<0) or (a>0 and k<0):
                continue
            source_inverse(19,(k,19*a))
            for typ in (0,1,2):
                for j in range(1,level+1):
                    # Extra powers j>=1 avoid bad growth; j=0 is included below
                    # through j-1. Pressure decays as r^-2.
                    if typ==2:
                        f=scalar(a,-2,j-1,False)
                        if a==0:
                            f=f*D**0
                        base=S.Matrix([0,0,0]); q=f
                    else:
                        f=scalar(a,typ,j-1,True)
                        phase=D**(-I*S.Float(omega)*k)
                        base=curl(f*phase*ez)
                        if typ==1:base=curl(base)
                        q=S.Integer(0)
                    if typ==2:q=q*D**(-I*S.Float(omega)*k)
                    # Reflection sends a -> -a, k unchanged; vector rotates.
                    flip={y:-y,z:-z}
                    reflected=S.diag(1,-1,-1)*base.subs(flip,simultaneous=True)
                    rq=q.subs(flip,simultaneous=True)
                    v=base+reflected; p=q+rq
                    if v==S.zeros(3,1) and p==0:continue
                    # k=0 requires real representation; otherwise use both
                    # quadratures (negative k recovered by real part).
                    for part in (0,1):
                        if k==0 and part==1:continue
                        factor=1 if part==0 else I
                        out.append((k,a,typ,j,part,factor*v,factor*p))
    return out


def grid(nr,nh,nt,na,shift=0.0):
    # finite radius quadrature for diagnostics only; not a tail enclosure.
    t=(np.arange(nr)+0.5+shift)/(nr+1)
    r=t/(1-t)
    h=(np.arange(nh)+0.5+shift)/nh
    theta=2*np.pi*(np.arange(na)+shift)/(19*na)
    s=2*np.pi*(np.arange(nt)+shift)/nt
    rr,hh,tt,ss=np.meshgrid(r,h,theta,s,indexing="ij")
    rho=rr*np.sqrt(1-hh*hh)
    pts=np.stack([rho*np.cos(tt),rho*np.sin(tt),rr*hh],axis=-1).reshape(-1,3)
    wt=(rr**2/(1-rr/(1+rr))**2).reshape(-1)
    wt=wt/wt.sum()
    return pts,ss.ravel(),wt


def ev(expr,pts):
    f=S.lambdify(xyz,expr,"numpy",cse=True)
    v=np.asarray(f(*pts.T),dtype=complex)
    return np.broadcast_to(v,(len(pts),))


def matrices(basis,pts,phase,omega,deadline):
    """Differentiate the same physical basis, never an amplitude surrogate."""
    n=len(pts); d=len(basis)
    V=np.zeros((n,3,d)); G=np.zeros((n,3,3,d))
    L=np.zeros((n,3,d)); P=np.zeros((n,d))
    for b,(k,a,typ,j,part,v,p) in enumerate(basis):
        if time.monotonic()>deadline:raise TimeoutError("basis deadline")
        e=np.exp(1j*k*phase)
        P[:,b]=(e*ev(p,pts)).real
        for i in range(3):
            V[:,i,b]=(e*ev(v[i],pts)).real
            for h in range(3):
                G[:,i,h,b]=(e*ev(S.diff(v[i],xyz[h]),pts)).real
            lap=sum(S.diff(v[i],t,2) for t in xyz)
            L[:,i,b]=(e*ev((S.Rational(1,2)+I*k*S.Float(omega))*v[i]-lap+S.diff(p,xyz[i]),pts)).real
        L[:,:,b]+=0.5*np.einsum("nij,nj->ni",G[:,:,:,b],pts)
    return V,G,L,P


def operators(M,wt):
    V,G,L,P=M
    sw=np.sqrt(wt)[:,None]
    def res(c):
        u=V@c; g=G@c
        return L@c+np.einsum("nij,nj->ni",g,u)
    def jac(c):
        u=V@c; g=G@c
        return L+np.einsum("nijd,nj->nid",G,u)+np.einsum("nij,njd->nid",g,V)
    def flat(v):return (v*sw).ravel()
    def jf(v):return (v*sw[:,:,None]).reshape(-1,V.shape[-1])
    return res,jac,flat,jf


def save(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data,indent=2,allow_nan=False)+"\n")
    tmp.replace(path)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--level",type=int,default=2)
    p.add_argument("--period",type=float,default=.36)
    p.add_argument("--amplitude",type=float,default=10.)
    p.add_argument("--steps",type=int,default=10)
    p.add_argument("--nfev",type=int,default=40)
    p.add_argument("--seconds",type=float,default=90.)
    p.add_argument("--nr",type=int,default=5)
    p.add_argument("--nh",type=int,default=5)
    p.add_argument("--out",type=Path,default=Path("Artifacts/ns369_similarity_candidate.json"))
    args=p.parse_args()
    if min(args.level,args.steps,args.nfev,args.nr,args.nh)<1 or min(args.period,args.seconds,args.amplitude)<=0:
        p.error("positive parameters required")
    deadline=time.monotonic()+args.seconds
    receipt={"source":"ad53419de079eb8f95f60313473374624a348546",
             "kind":"independent floating-point candidate; no continuum or kernel acceptance",
             "status":"started","fields":{f:"unpaid" for f in FIELDS},"history":[]}
    save(args.out,receipt)
    try:
        omega=2*np.pi/args.period
        basis=build_basis(args.level,omega)
        receipt["basis"]=[list(b[:5]) for b in basis]
        receipt["period"]=args.period
        # Quadratic output reaches twice the input cutoff. >=4K+1 samples
        # distinguish all output frequencies without circular aliasing.
        nt=na=4*args.level+1
        pts,phase,wt=grid(args.nr,args.nh,nt,na)
        M=matrices(basis,pts,phase,omega,deadline)
        V,G,L,P=M
        r,J,flat,jf=operators(M,wt)
        energy=np.einsum("n,nid,nie->de",wt,V,V)
        norms=np.sqrt(np.diag(energy))
        # Scale columns numerically, including pressure-only columns.
        scale=np.maximum(norms,np.linalg.norm(jf(L),axis=0))
        scale=np.maximum(scale,1e-12)
        c=np.zeros(len(basis))
        for i,b in enumerate(basis):
            if b[2]!=2 and norms[i]>1e-12:
                c[i]=args.amplitude/norms[i];break
        else:raise ValueError("no nonzero velocity basis")
        # Forced seed is exact at the collocation level, then remove its
        # entire physical residual. Nontriviality tracked, not enforced by
        # adding a hidden force or accepting a constrained residual.
        force=flat(r(c)); receipt["seed_norm"]=float(np.sqrt(c@energy@c))
        for h in np.linspace(1,0,args.steps+1):
            def guard(v):
                if time.monotonic()>deadline:raise TimeoutError("solve deadline")
                return v
            result=least_squares(lambda v:guard(flat(r(v/scale))-h*force),
                                 c*scale,jac=lambda v:guard(jf(J(v/scale))/scale),
                                 max_nfev=args.nfev,ftol=1e-10,gtol=1e-10,xtol=1e-10)
            c=result.x/scale
            receipt["coefficients"]=c.tolist()
            receipt["history"].append({"force_fraction":float(h),"residual":float(np.linalg.norm(result.fun)),
                "unforced_residual":float(np.linalg.norm(flat(r(c)))),"velocity_norm":float(np.sqrt(max(0,c@energy@c))),
                "nfev":result.nfev,"solver_success":bool(result.success)})
            receipt["status"]="continuation"
            save(args.out,receipt)
        # Actual sample Gram and symmetric stretching form, with physical
        # coordinate Jacobian weights. NOT original continuous CellCalculus.
        W=V@c; grad=G@c
        strain=(grad+grad.transpose(0,2,1))/2
        stretch=np.einsum("n,nid,nij,nje->de",wt,V,strain,V)
        stiffness=np.einsum("n,nijd,nije->de",wt,G,G)
        A=jf(J(c))
        u,s,vh=np.linalg.svd(A,full_matrices=False)
        # Numerical adjoint singular directions in residual space, retained
        # with actual source rows. Not global PDE adjoint fields.
        count=min(3,len(s))
        adj=u[:,-count:]
        receipt["diagnostics"]={"singular_values":s.tolist(),
            "adjoint_residuals":np.linalg.norm(A.T@adj,axis=0).tolist(),
            "actuator_pairings":(adj.T@flat(r(c))).tolist(),
            "max_sample_divergence":float(np.max(np.abs(np.trace(grad,axis1=1,axis2=2)))),
            "mass_matrix":energy.tolist(),"stiffness_matrix":stiffness.tolist(),
            "stretch_matrix":stretch.tolist()}
        receipt["status"]="unforced_candidate_not_certified"
        save(args.out,receipt)
        # Independent offset collocation; catches fit-grid overfitting.
        pp,ph,ww=grid(args.nr,args.nh,nt,na,shift=.19)
        MM=matrices(basis,pp,ph,omega,deadline)
        rr,_,ff,_=operators(MM,ww)
        receipt["diagnostics"]["holdout_residual"]=float(np.linalg.norm(ff(rr(c))))
        receipt["diagnostics"]["holdout_max_residual"]=float(np.max(np.abs(rr(c))))
        receipt["status"]="diagnostics_complete_not_certified"
    except TimeoutError as e:
        receipt["status"]="checkpoint_timeout";receipt["reason"]=str(e)
    except Exception as e:
        receipt["status"]="failed";receipt["reason"]=repr(e)
        save(args.out,receipt);raise
    save(args.out,receipt)
    print(receipt["status"],args.out)

if __name__=="__main__":main()
