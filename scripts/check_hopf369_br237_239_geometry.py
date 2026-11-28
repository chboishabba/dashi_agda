#!/usr/bin/env python3
"""BR237--239: metric-compatible wall connection and common-metric material.
Finite geometric comparator; not Einstein evolution or continuum acceptance.
"""
import argparse
import numpy as np
import sympy as s
from scipy.optimize import root


def wall():
    from check_hopf369_br_curvature_energy import carrier,P
    _,_,X,G,Y,_,J,*_=carrier()
    eta=s.diag(-1,1,1,1,1); n=s.eye(5)[:,4]
    u=s.Matrix([*s.symbols('u:4',real=True),0]); K=u*n.T*eta-n*u.T*eta
    assert K*n==u and K.T*eta+eta*K==s.zeros(5)
    N=n*n.T*eta; dN=u*n.T*eta+n*u.T*eta
    assert dN==K*N-N*K
    # Original BR207 tensor representation, with symbolic normal derivative.
    L=s.Matrix(10,10,lambda a,b:K[P[a][0],P[b][0]]*int(P[a][1]==P[b][1])-K[P[a][0],P[b][1]]*int(P[a][1]==P[b][0])-K[P[a][1],P[b][0]]*int(P[a][0]==P[b][1])+K[P[a][1],P[b][1]]*int(P[a][0]==P[b][0]))
    T=s.kronecker_product(L,s.eye(10))+s.kronecker_product(s.eye(10),L)
    O=G.inv()*X.T*T*X
    assert X*O==T*X
    def wedge(a,b):
        return s.Matrix(10,10,lambda i,j:a[P[i][0],P[j][0]]*b[P[i][1],P[j][1]]+b[P[i][0],P[j][0]]*a[P[i][1],P[j][1]]-a[P[i][0],P[j][1]]*b[P[i][1],P[j][0]]-b[P[i][0],P[j][1]]*a[P[i][1],P[j][0]])
    m=s.symbols('m:9'); M=s.zeros(5); M[:4,:4]=s.Matrix(4,4,list(Y*s.Matrix(m)))
    dM=K*M+M*K.T; NN=n*n.T; dNN=u*n.T+n*u.T
    assert (dM*eta*n+M*eta*u).applyfunc(s.expand)==s.zeros(5,1)
    V=-wedge(eta,M)+3*wedge(NN,M)
    dV=-wedge(eta,dM)+3*wedge(dNN,M)+3*wedge(NN,dM)
    assert (s.Matrix(list(V))-X*J*s.Matrix(m)).applyfunc(s.expand)==s.zeros(100,1)
    assert (s.Matrix(list(dV))-X*O*J*s.Matrix(m)).applyfunc(s.expand)==s.zeros(100,1)
    # Negative control: ambient derivative does not preserve the jump image.
    Pi=J*(J.T*J).inv()*J.T
    assert (s.eye(35)-Pi)*O*J!=s.zeros(35,9)
    print('BR237 PASS metric-compatible adapted connection, symbolic actual jump derivative, nonzero ambient defect')


def material():
    import check_hopf369_p0ag as d
    z=d.z; B,R=d.surface(); H0,Hs,V=d.assembly()
    S=np.block([[np.zeros((54,54)),z.C.T],[-z.C,np.zeros((36,36))]])
    L=np.vstack((z.J,np.zeros((36,108)))); charges=np.array([1.,-1.]); dt=.025
    # A single conformal spatial metric h(t)=a(t)^2 h0. Zero shift;
    # Hodge matrices scale as 1/a, proper interior volumes as a^3.
    # Reservoirs remain external fixed-volume selected loads.
    def geometry(a):
        assert a>0
        v=V.copy(); v[:27]*=a**3
        return H0/a,v
    energy=lambda n,x,H,v:np.sum(n*(np.log(n/v[:,None])-1))+.5*x@H@x
    for sign in (-1,1):
        n=np.ones((33,2))*V[:,None]; x=np.r_[np.zeros(54),z.C@np.sin(np.arange(54))*.1]; surf=np.zeros(54)
        H,vol=geometry(1.); initial=n.sum(axis=0); worst=0.; vwtotal=0.; hwtotal=0.
        for j in range(4):
            a=1+sign*.015*(j+1); H1,V1=geometry(a); K=(H+H1)/2
            assert np.linalg.eigvalsh(H1)[0]>0 and V1.min()>0
            A=np.eye(90)-dt/2*S@K; free=np.linalg.solve(A,x); W=np.linalg.solve(A,dt/2*L)
            # Conductance scales as area/length for uniformly scaled interior.
            conduct=np.full(108,.1*a) # selected scaled port conductance
            def terms(u):
                nn=np.exp(u[:n.size].reshape(n.shape)); v=u[n.size:]; c=nn/V1[:,None]; xi=v[:,None]*charges
                aa=c[z.left]*z.bern(-xi); bb=c[z.right]*z.bern(xi); m=conduct[:,None]*(aa-bb); i=m@charges; mid=free-W@i
                return nn,v,aa,bb,m,i,mid
            def residual(u):
                nn,v,aa,bb,m,i,mid=terms(u)
                return np.r_[(nn-n-dt*z.Vhat@m).ravel(),v-L.T@K@mid]
            sol=root(residual,np.r_[np.log(n).ravel(),L.T@K@free],options={'xtol':1e-10})
            nn,v,aa,bb,m,i,mid=terms(sol.x); xn=2*mid-x; sn=surf+dt*R@i
            assert np.all(np.isfinite(sol.x)) and min(nn.min(),aa.min(),bb.min())>0
            diss=dt*np.sum(m*(np.log(aa)-np.log(bb))); rem=np.sum(n*np.log(n/nn)-n+nn)
            hw=(xn@(H1-H)@xn+x@(H1-H)@x)/4; vw=-np.sum(n*np.log(V1/vol)[:,None])
            err=abs(energy(nn,xn,H1,V1)-energy(n,x,H,vol)-hw-vw+diss+rem)
            gauss=np.max(abs(-z.G@xn[:54]-z.Q@(nn[:27]@charges)-B@sn))
            worst=max(worst,err,gauss,np.max(abs(z.Z@xn[54:])),np.max(abs(residual(sol.x))),np.max(abs(nn.sum(axis=0)-initial)),abs(sn.sum()-(nn[27:]@charges).sum()))
            assert min(diss,rem)>=-1e-10 and worst<1e-8
            n,x,surf,H,vol=nn,xn,sn,H1,V1; vwtotal+=vw; hwtotal+=hw
        print('BR238 PASS same-metric conformal history',sign,'residual',worst,'volume work',vwtotal,'Hodge work',hwtotal)


def scaling():
    a=s.symbols('a',positive=True); h=s.Matrix([[3,1,0],[1,4,1],[0,1,2]])
    h1=a*a*h; v=s.sqrt(h.det()); v1=s.sqrt(h1.det())
    assert s.simplify(v1-a**3*v)==0
    assert (v1*h1.inv()-a*v*h.inv()).applyfunc(s.simplify)==s.zeros(3)
    assert (h1/v1-h/(a*v)).applyfunc(s.simplify)==s.zeros(3)
    print('BR239 PASS exact common metric Hodge and volume scaling')

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--part',required=True,choices=['wall','material','scaling']); globals()[p.parse_args().part]()
