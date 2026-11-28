"""Original BR280 G4 data, coupled 4D reduced Einstein / conservative RMHD.
Finite central box diagnostic; no certified boundary or continuum solution.
"""
import argparse, inspect
import numpy as np
import check_hopf369_br240_metric_history as vac
import check_hopf369_br280_g4_york as src
from check_hopf369_br230_233_dynamic_cut import primitive

# Dimension-independent BR240 tensor contractions; only spatial derivative
# allocation changes. The four-dimensional trace reversal is explicit below.
ns=dict(vars(vac))
exec(inspect.getsource(vac.spatial).replace('(5,5,5)','(4,4,4)'),ns)
exec(inspect.getsource(vac.jets),ns)
exec(inspect.getsource(vac.acceleration),ns)
spatial,jets,acc=ns['spatial'],ns['jets'],ns['acceleration']
C=src.K0-2*src.P0

def adm(g):
    h=g[...,1:,1:]; M=np.linalg.cholesky(h).swapaxes(-1,-2); I=np.linalg.inv(h)
    beta=np.einsum('...ij,...j->...i',I,g[...,0,1:]); alpha=np.sqrt(np.sum(beta*g[...,0,1:],axis=-1)-g[...,0,0]); root=np.sqrt(np.linalg.det(h))
    return h,M,beta,alpha,root

def initial(n):
    x=np.linspace(-1.5,1.5,n); dx=x[1]-x[0]; X=np.stack(np.meshgrid(x,x,x,indexing='ij'),axis=-1); r=np.linalg.norm(X,axis=-1); mu=np.divide(X[...,2],r,out=np.zeros_like(r),where=r>0)
    radial=src.radial_functions(); read,p,*_=src.solve(radial); psi,_=read(np.maximum(r,1e-6),mu); psi[r==0]=p
    Y=src.york(X,radial); B=src.magnetic(X); g=np.zeros(X.shape[:-1]+(4,4));g[...,0,0]=-1;g[...,1:,1:]=psi[...,None,None]**4*np.eye(3)
    K=Y/psi[...,None,None]**2+np.sqrt(3*src.KAP*(src.K0-src.P0))*g[...,1:,1:]/3
    v=np.zeros_like(g);v[...,1:,1:]=-2*K;d=spatial(g,dx);I=np.linalg.inv(g);v[...,0,0]=-np.einsum('...ij,...ij->...',I[...,1:,1:],v[...,1:,1:]);v[...,0,1:]=v[...,1:,0]=np.einsum('...jk,...jki->...i',I[...,1:,1:],d[...,1:,1:,1:])-.5*np.einsum('...jk,...ijk->...i',I[...,1:,1:],d[...,1:,1:,1:])
    b=src.EPS*B/psi[...,None]**4;j=src.SIGN*np.sqrt(src.K0)*src.EPS*B/psi[...,None]**8;rho=src.K0-src.P0+np.sum(b*b,axis=-1)
    U=np.concatenate((-psi[...,None]**6*rho[...,None],psi[...,None]**8*j,src.EPS*B),axis=-1)
    assert np.max(abs(jets(g,v,dx)[3]))<1e-10
    return g,v,U,dx

def matter(g,U):
    h,M,beta,alpha,root=adm(g); I=np.linalg.inv(g);T=np.zeros_like(g);transport=np.zeros_like(U[...,4:]);margin=1.
    for idx in np.ndindex(U.shape[:-1]):
        a=alpha[idx];m=M[idx];r=root[idx];be=beta[idx];u=U[idx];j=u[1:4]/r;rho=(-u[0]/r+be@j)/a; jo=np.linalg.solve(m.T,j);B=m@(u[4:]/r)
        q,w,B,p=primitive(np.r_[rho,jo,B[1:]],B[0],C);E=-np.cross(w,B);S=q*np.outer(w,w)+p*np.eye(3)+(B@B+E@E)/2*np.eye(3)-np.outer(B,B)-np.outer(E,E)
        nc=np.r_[-a,0.,0.,0.]; jc=np.r_[be@j,j];Sc=m.T@S@m; spatialS=np.block([[np.array([[be@Sc@be]]),(Sc@be)[None,:]],[(Sc@be)[:,None],Sc]])
        T[idx]=rho*np.outer(nc,nc)+np.outer(nc,jc)+np.outer(jc,nc)+spatialS
        transport[idx]=a*np.linalg.solve(m,w)-be; margin=min(margin,p,p+C,1-w@w)
    mixed=I@T;up=mixed@I;den=alpha*root
    assert np.max(abs(den[...,None]*mixed[...,0,:]-U[...,:4]))<1e-9
    F=np.zeros(U.shape[:-1]+(3,7));F[...,:4]=den[...,None,None]*mixed[...,1:,:]
    F[...,4:]=transport[..., :,None]*U[...,None,4:]-U[...,4:,None]*transport[...,None,:]
    return T,up,F,den,margin

def run(n,steps,dt):
    g,v,U,dx=initial(n);g0=g.copy();sl=(slice(2,-2),)*3;worst=0.;margin=1.
    def rhs(g,v,U):
        T,up,F,den,m=matter(g,U);I=np.linalg.inv(g);tr=np.einsum('...ij,...ij->...',I,T);S=src.KAP*(T-.5*g*tr[...,None,None]);a=acc(g,v,dx)-2*S/I[...,0,0,None,None]
        d=spatial(g,dx);d[...,0,:,:]=v;source=np.zeros_like(U);source[...,:4]=.5*den[...,None]*np.einsum('...ij,...kij->...k',up,d)
        du=source.copy()
        for i in range(3):
            fi=F[...,i,:];du-=(np.roll(fi,-1,axis=i)-np.roll(fi,1,axis=i))/(2*dx)
        vv=v.copy()
        for i in range(3):
            for k in (0,-1):
                idx=[slice(None)]*3;idx[i]=k;idx=tuple(idx);vv[idx]=0;a[idx]=0;du[idx]=0
        return vv,a,du,m,source
    def divB(U):return sum((np.roll(U[...,4+i],-1,axis=i)-np.roll(U[...,4+i],1,axis=i))/(2*dx) for i in range(3))
    b0=divB(U); initial_gauge=np.max(abs(jets(g,v,dx)[3]));
    for _ in range(steps):
        w,a,b,m,_=rhs(g,v,U);wm,am,bm,mm,source=rhs(g+dt*w/2,v+dt*a/2,U+dt*b/2);old=U.copy();g+=dt*wm;v+=dt*am;U+=dt*bm; margin=min(margin,m,mm);worst=max(worst,np.max(abs((U-old)-dt*bm)))
    _,_,_,_,m=matter(g,U);margin=min(margin,m);gauge=np.max(abs(jets(g,v,dx)[3][sl]));bd=np.max(abs((divB(U)-b0)[sl]));assert margin>0 and bd<1e-10 and worst<1e-12
    print('BR283-284',n,steps,dt,'initial gauge',initial_gauge,'final gauge',gauge,'magnetic divergence drift',bd,'update arithmetic',worst,'margin',margin,'metric change',np.max(abs(g-g0)),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);p.add_argument('--steps',type=int,default=2);p.add_argument('--dt',type=float,default=.002);a=p.parse_args();run(a.n,a.steps,a.dt)
