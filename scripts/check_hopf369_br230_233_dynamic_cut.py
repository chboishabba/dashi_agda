#!/usr/bin/env python3
"""BR230/232/233: donor-based finite evolution cut. Run each part under 90s.
No curved continuum or native kernel acceptance. See companion roadmap.
"""
import argparse
import numpy as np
from scipy.optimize import brentq, root

def periodic():
    import sympy as s
    from check_hopf369_br_curvature_energy import carrier,P,Q
    from check_hopf369_br205_wall_lorentz import run as tangent
    from check_hopf369_br207_moving_normal import run as normal
    _,V,X,G,Y,H,J,*_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    tangent(X,G,Y,H,J,F)
    normal(X,G,Y,J,F)
    # In an adapted moving frame J is constant, and each tangent generator
    # intertwines it. Test the induced exact left inverse and projection.
    L=(J.T*J).inv()*J.T
    assert L*J==s.eye(J.cols)
    K=J*L
    assert K*K==K and K*J==J
    # A covariant derivative in ambient frame differs by the frame velocity.
    # For J(t)=U(t) J V(t)^-1, J'=A J-J B; corrected D=partial-A/B.
    # The donor generator identities above instantiate this relation.
    print('BR230 donor tangent/normal replay; adapted image split; no curved estimate')

def conserved(q,v,B,C):
    b=B@B; w=q*(1-v@v); p=(w-C)/2
    if q<=0 or w<=abs(C): raise ValueError('inadmissible')
    return np.r_[q-p+b/2+(b*(v@v)-(B@v)**2)/2,(q+b)*v-(B@v)*B,B[1:]]

def primitive(U,Bx,C):
    rho=U[0]; j=U[1:4]; B=np.r_[Bx,U[4:6]]; b=B@B
    jp=B*(B@j)/b if b else j.copy(); jt=j-jp
    a=jp@jp; d=jt@jt
    def v(q): return jp/q+jt/(q+b)
    def w(q): return q*(1-v(q)@v(q))
    lo=1e-12; hi=max(1.,abs(C)+np.linalg.norm(j)+b)
    while w(hi)<=abs(C): hi*=2
    qmin=lo if w(lo)>abs(C) else brentq(lambda q:w(q)-abs(C),lo,hi,xtol=1e-13)
    phi=lambda q:q+a/q+d/(q+b)-(2*rho-C-b)
    if phi(qmin)>=0: raise ValueError('no positive-pressure root')
    while phi(hi)<0: hi*=2
    q=brentq(phi,qmin,hi,xtol=1e-13); vv=v(q); p=(w(q)-C)/2
    assert vv@vv<1 and p>0 and p+C>0
    assert np.max(abs(conserved(q,vv,B,C)-U))<1e-9
    return q,vv,B,p

def flux(U,Bx,C):
    q,v,B,p=primitive(U,Bx,C); b=B@B
    E=-np.cross(v,B); stress=q*np.outer(v,v)+p*np.eye(3)+(b+E@E)/2*np.eye(3)-np.outer(B,B)-np.outer(E,E)
    return np.r_[U[1],stress[:,0],v[0]*B[1:]-Bx*v[1:]]

def g4():
    # Flat periodic finite-volume comparator, not P0H York evolution.
    C=.5; Bx=.3; N=32; phase=2*np.pi*np.arange(N)/N
    U=np.array([conserved(2+.1*np.cos(t),np.array([.12,.09*np.sin(t),.05]),np.array([Bx,.25+.04*np.sin(t),.1]),C) for t in phase])
    initial=U.sum(axis=0); minimum=1.
    for _ in range(20):
        F=np.array([flux(u,Bx,C) for u in U])
        face=(F+np.roll(F,-1,axis=0)-np.roll(U,-1,axis=0)+U)/2
        U-=.2*(face-np.roll(face,1,axis=0))
        for u in U:
            q,v,B,p=primitive(u,Bx,C)
            minimum=min(minimum,1-v@v,p,p+C)
        assert np.max(abs(U.sum(axis=0)-initial))<1e-10
    print('BR232 flat periodic conservative evolution, minimum physical margin',minimum)

def material():
    import check_hopf369_p0ag as d
    z=d.z
    B,R=d.surface(); H0,Hs,V=d.assembly()
    S=np.block([[np.zeros((54,54)),z.C.T],[-z.C,np.zeros((36,36))]])
    L=np.vstack((z.J,np.zeros((36,108))))
    charges=np.array([1.,-1.]); dt=.025
    energy=lambda n,x,H,V:np.sum(n*(np.log(n/V[:,None])-1))+.5*x@H@x
    for sign in (-1,1):
        n=np.ones((33,2))*V[:,None]; x=np.r_[np.zeros(54),z.C@np.sin(np.arange(54))*.1]; surf=np.zeros(54)
        H=H0.copy(); vol=V.copy(); initial=n.sum(axis=0)
        worst=0.; volume_work=0.
        for j in range(4):
            # Prescribed positive volume history on original P0AG cells;
            # no claim that it solves Einstein or induces H1.
            H1=H0+sign*(j+1)*dt*Hs
            V1=V.copy(); V1[:27]*=1+sign*.01*(j+1)*np.cos(np.arange(27))
            assert np.min(V1)>0 and np.linalg.eigvalsh(H1)[0]>0
            K=(H+H1)/2; A=np.eye(90)-dt/2*S@K
            free=np.linalg.solve(A,x); W=np.linalg.solve(A,dt/2*L)
            def terms(u):
                nn=np.exp(u[:n.size].reshape(n.shape)); v=u[n.size:]
                c=nn/V1[:,None]; xi=v[:,None]*charges
                a=c[z.left]*z.bern(-xi); b=c[z.right]*z.bern(xi)
                m=.1*(a-b); i=m@charges; mid=free-W@i
                return nn,v,a,b,m,i,mid
            def residual(u):
                nn,v,a,b,m,i,mid=terms(u)
                return np.r_[(nn-n-dt*z.Vhat@m).ravel(),v-L.T@K@mid]
            sol=root(residual,np.r_[np.log(n).ravel(),L.T@K@free],options={'xtol':1e-10})
            nn,v,a,b,m,i,mid=terms(sol.x); xn=2*mid-x; sn=surf+dt*R@i
            assert np.all(np.isfinite(sol.x)) and nn.min()>0 and a.min()>0 and b.min()>0
            diss=dt*np.sum(m*(np.log(a)-np.log(b))); rem=np.sum(n*np.log(n/nn)-n+nn)
            metric=(xn@(H1-H)@xn+x@(H1-H)@x)/4
            vw=-np.sum(n*np.log(V1/vol)[:,None])
            err=abs(energy(nn,xn,H1,V1)-energy(n,x,H,vol)-metric-vw+diss+rem)
            gauss=np.max(abs(-z.G@xn[:54]-z.Q@(nn[:27]@charges)-B@sn))
            worst=max(worst,err,gauss,np.max(abs(z.Z@xn[54:])),np.max(abs(residual(sol.x))),np.max(abs(nn.sum(axis=0)-initial)),abs(sn.sum()-(nn[27:]@charges).sum()))
            assert diss>=-1e-10 and rem>=-1e-10 and worst<1e-8
            n,x,surf,H,vol=nn,xn,sn,H1,V1; volume_work+=vw
        print('BR233 P0AG variable-volume comparator',sign,'worst',worst,'volume work',volume_work)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--part',required=True,choices=['periodic','g4','material']); globals()[p.parse_args().part]()
