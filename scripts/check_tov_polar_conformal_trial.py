"""Original repaired TOV radial-material polar trials, fixed conformal metric.
Finite Galerkin diagnostic only, compact support and no moving surface.
"""
import numpy as np
import sympy as s
from scipy.integrate import cumulative_trapezoid
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import spsolve
from numpy.polynomial.legendre import leggauss


def coefficients():
    x=s.symbols('x'); l=s.Rational(1,10); p=l/(8*s.pi)
    rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
    f=1-l*(2+l)*(x/3-x*x/5)
    P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f)
    a=(rho+pt)/2; d=(rho+pr)/(2*f); V=rho-2*a-d*f
    r,R,j=s.symbols('r R j',positive=True)
    T=d.subs(x,R*R)*f.subs(x,r*r)*j*j+2*a.subs(x,R*R)*R*R/r**2
    ev=lambda z:z.subs({R:r,j:1})
    expressions=[f.subs(x,r*r),V.subs(x,r*r),d.subs(x,r*r),p*(1-r*r)/2,
                 ev(s.diff(T,R)),ev(s.diff(T,j)),ev(s.diff(T,R,2)),ev(s.diff(T,R,j)),ev(s.diff(T,j,2)),
                 ev(s.diff(V.subs(x,R*R),R)),ev(s.diff(V.subs(x,R*R),R,2)),s.diff(f.subs(x,r*r),r),r*l*P.subs(x,r*r)/f.subs(x,r*r)]
    return s.lambdify(r,expressions,'numpy')


def run(coef,n,ell,Rmax):
    # Unit sphere harmonic norm; radial displacement U Y_lm n.
    L=ell*(ell+1); M=7/500
    nodes=np.r_[np.linspace(0,1,n+1),np.geomspace(1,Rmax,n+1)[1:]]
    t,wt=leggauss(6); left=nodes[:-1,None]; dr=np.diff(nodes)[:,None]
    r=left+dr*(t+1)/2; weights=dr*wt/2; inside=r<1
    ri=r[inside]; f=1-2*M/r; V=np.zeros_like(r)
    fi,Vi,d,c,TR,Tj,TRR,TRj,Tjj,VR,VRR,fr,nu=coef(ri)
    f[inside]=fi; V[inside]=Vi
    # Lapse quadrature on a dense original radial mesh, independent of FE mesh.
    rr=np.linspace(0,1,20001); _,_,_,_,_,_,_,_,_,_,_,_,nup=coef(np.maximum(rr,1e-9))
    nuint=cumulative_trapezoid(nup,rr,initial=0)
    N=np.sqrt(f); N[inside]=np.sqrt(1-2*M)*np.exp(np.interp(ri,rr,nuint)-nuint[-1])
    w=r*r/np.sqrt(f); A=r*r*np.sqrt(f)
    # Smooth compact annular trial, with vanishing first derivative at edges.
    aa,bb=.15,.85; q=(ri-aa)*(bb-ri); U=np.where(q>0,q**3,0); Up=np.where(q>0,3*q*q*(aa+bb-2*ri),0)
    U=U/.001; Up=Up/.001
    T1=TR*U+Tj*Up; V1=VR*U
    T2=TRR*U*U+2*TRj*U*Up+Tjj*Up*Up+2*d*L*U*U/ri**2
    V2=VRR*U*U
    S=np.zeros_like(r); S[inside]=2*np.pi*(T1+V1)
    # Ground-state solve chi=N v; weak form with angular potential.
    shape=np.array([(1-t)/2,(1+t)/2]); deriv=np.array([-1,1])[:,None,None]/dr
    rows=[];cols=[];vals=[];rhs=np.zeros(len(nodes))
    for i in range(2):
        np.add.at(rhs,np.arange(len(nodes)-1)+i,np.sum(weights*w*N*S*shape[i],axis=1))
        for j in range(2):
            vals.extend(np.sum(weights*N*N*(A*deriv[i]*deriv[j]+w*L/r**2*shape[i]*shape[j]),axis=1))
            rows.extend(np.arange(len(nodes)-1)+i);cols.extend(np.arange(len(nodes)-1)+j)
    H=coo_matrix((vals,(rows,cols)),shape=(len(nodes),len(nodes))).tocsr()
    v=np.zeros(len(nodes)); v[1:-1]=spsolve(H[1:-1,1:-1],rhs[1:-1])
    assert np.max(np.abs((H@v-rhs)[1:-1]))<1e-8
    chi=(N*(v[:-1,None]*shape[0]+v[1:,None]*shape[1]))[inside]
    # Target-normalized strain, angular integrated (H norm 1).
    Z=2*Up-fr/fi*U-4*chi; Y=2*U/ri-4*chi
    # off-diagonal normalized radial/angular strain U/(r sqrt(f))*D_A H.
    repair=c*((Z+2*Y)**2-Z*Z-2*Y*Y-2*L*U*U/(ri**2*fi))
    F2=T2+V2+2*chi*T1+10*chi*V1+20*chi*chi*Vi+repair
    energy=np.sum(weights[inside]*N[inside]*w[inside]*F2)
    assert np.isfinite(energy)
    print(ell,n,Rmax,'signed ADM trial',energy,flush=True)
    return energy


if __name__=='__main__':
    coef=coefficients()
    for ell in (1,2,3,4):
        for n,R in ((64,8),(128,8),(128,16),(256,16)):run(coef,n,ell,R)
