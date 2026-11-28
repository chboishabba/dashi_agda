"""Matched incident/reflected port on the existing finite spatial integrator.
Synthetic source and recovery efficiencies; not a calibrated Earth/ground port.
"""
import json
import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.optimize import brentq
from solar_earth_spatial_transport import Grid, cell, verify_step


def port(z,sl,weight,Y,a,h):
    """a is prescribed incident sqrt(power); outgoing wave depends on E.
    Normalized tangential x=sqrt(weight)*E, weight=dx*eps, Y>0.
    """
    a=np.asarray(a,float)
    if a.shape!=(2,) or not np.isfinite([*a,weight,Y,h]).all() or min(weight,Y)<=0 or h<=0:
        raise ValueError('finite positive port parameters required')
    alpha=Y/weight; root=np.sqrt(alpha); x=z[sl.start:sl.start+2].copy()
    r=np.exp(-alpha*h); d=root*x-2*a
    final=r*x-2*a*np.expm1(-alpha*h)/root
    # outgoing(t)=a+d exp(-alpha*t); independently integrate its square.
    i1=-np.expm1(-alpha*h)/alpha; i2=-np.expm1(-2*alpha*h)/(2*alpha)
    G=np.array([[h,i1],[i1,i2]]); ev,V=np.linalg.eigh(G)
    if ev[0]<-1e-13*h: raise ArithmeticError('negative outgoing Gram')
    feat=(np.sqrt(np.maximum(ev,0))[:,None]*V.T@np.stack([a,d])).ravel()
    incident=h*(a@a); outgoing=feat@feat
    residual=(final@final-x@x)/2-incident+outgoing
    assert abs(residual)<1e-10*max(1.,incident,outgoing,x@x)
    out=z.copy(); out[sl.start:sl.start+2]=final
    return out,float(incident),feat


def gross(p,q):
    """Positive/negative integrated work for linear power over one unit interval."""
    if p>=0 and q>=0: return (p+q)/2,0.
    if p<=0 and q<=0: return 0.,-(p+q)/2
    return max(p,q)**2/(2*abs(q-p)),min(p,q)**2/(2*abs(q-p))


class IncidentGrid:
    def __init__(self,grid,h,Y):
        if grid.periodic or len(Y)!=2 or not all(np.isfinite(v) and v>0 for v in Y): raise ValueError('two positive exterior admittances')
        self.g=grid; self.h=h; self.Y=Y; self.p=grid.prepare(h)
        self.factors=[]
        for _,Q in self.p[2]:
            ev,V=np.linalg.eigh(sum(Q[1:])); assert min(ev)>-1e-12
            self.factors.append(np.sqrt(np.maximum(ev,0))[:,None]*V.T)

    def step(self,z,a,ctrl):
        g,h=self.g,self.h; start=z.copy(); incoming=0.; features=[]; a=np.asarray(a,float).reshape(2,2)
        def boundary(z,i):
            j=0 if i==0 else g.n-1; sl=g.local[j][0]
            z,w,f=port(z,sl,g.dx*g.eps[j],self.Y[i],a[i],h/2)
            return z,w,f
        for i in (0,1):
            z,w,f=boundary(z,i); incoming+=w; features.append(f)
        first=z.copy(); z,w,_=verify_step(g,z,h,self.p,controller=ctrl); last=z.copy()
        # Existing zero-boundary controller half kicks: integrate sign crossing per cell.
        delta=h/2*ctrl; P=N=0.
        for sl,_,_ in g.local:
            for x in (first,last-delta):
                p=delta[sl]@x[sl]; q=delta[sl]@(x[sl]+delta[sl]); plus,minus=gross(p,q); P+=plus; N+=minus
        assert abs(P-N-w['controller'])<1e-10
        material=[F@v for F,v in zip(self.factors,w['material_inputs'])]
        mat=float(w['material_loss'].sum()); load=float(w['load'].sum())
        assert abs(sum(v@v for v in material)-mat)<1e-10
        for i in (1,0):
            z,v,f=boundary(z,i); incoming+=v; features.append(f)
        reflected=sum(v@v for v in features)
        residual=(z@z-start@start)/2+mat+load+reflected-incoming-P+N
        assert abs(residual)<1e-10
        return z,np.array([incoming,reflected,mat,load,P,N]),np.concatenate(features+material)

    def run(self,source,ports,u,observe):
        z=np.zeros(self.g.size); y=0.; ledger=np.zeros(6); features=[]
        for a,c in zip(source,u.reshape(len(source),-1)):
            z,w,f=self.step(z,a,ports@c); y+=self.h*observe@z; ledger+=w; features.append(f)
        I,O,Q,L,P,N=ledger; stored=z@z/2
        assert abs(stored+O+Q+L-I-P+N)<1e-10
        return np.r_[z,y],ledger,np.concatenate(features)


def lift(m,n,ports,observe):
    g=m.g; h=m.h; z=np.zeros(g.size); no=np.zeros((2,2)); c0=np.zeros(g.size)
    A=np.column_stack([m.step(v,no,c0)[0] for v in np.eye(g.size)])
    B=np.column_stack([m.step(z,no,v)[0] for v in ports.T]); L=np.column_stack([m.step(z,v.reshape(2,2),c0)[0] for v in np.eye(4)])
    AA=np.zeros((g.size+1,g.size+1)); AA[:-1,:-1]=A; AA[-1,:-1]=h*observe@A; AA[-1,-1]=1
    def history(M):
        aug=np.vstack([M,h*observe@M]); return np.column_stack([np.linalg.matrix_power(AA,n-1-k)@aug for k in range(n)])
    return history(L),history(B)


def net(w,eta_in,eta_rec,aux):
    I,O,Q,L,P,N=w
    if not 0<eta_in<=1 or not 0<=eta_rec<=1 or aux<0: raise ValueError('invalid efficiency/cost')
    return float(L-P/eta_in+eta_rec*N-aux)


def optimize(m,source,ports,observe,B,x,radius):
    _,_,V=np.linalg.svd(B,full_matrices=True); rank=np.linalg.matrix_rank(B); Z=V[rank:].T
    assert np.linalg.norm(B@Z)<1e-10 and np.linalg.norm(x@Z)<1e-10
    target,w,f=m.run(source,ports,x,observe); F=np.column_stack([m.run(source,ports,x+d,observe)[2]-f for d in Z.T])
    U,sv,Vh=np.linalg.svd(F,full_matrices=False); g=sv*(U.T@f)
    # Minimize outgoing plus material loss on the endpoint-preserving ball.
    keep=sv>sv[0]*1e-12; v=np.zeros_like(sv); v[keep]=-g[keep]/sv[keep]**2; lam=0.
    if np.linalg.norm(v)>radius:
        def norm(l): return np.linalg.norm(g/(sv**2+l))
        hi=1.
        while norm(hi)>radius: hi*=2
        lam=brentq(lambda l:norm(l)-radius,1e-15,hi,xtol=1e-14); v=-g/(sv**2+lam)
    d=Vh.T@v; u=x+Z@d; final,w1,f1=m.run(source,ports,u,observe)
    kkt=np.linalg.norm(F.T@(f+F@d)+lam*d)
    assert kkt<1e-9 and np.linalg.norm(d)<=radius+1e-9 and np.linalg.norm(final-target)<1e-9
    assert np.linalg.norm(f1-f-F@d)<1e-9
    assert abs(net(w1,1,1,0)-(w1[0]-f1@f1))<1e-9
    assert net(w1,1,1,0)>=net(w,1,1,0)-1e-10
    return u,w1,Z,kkt


def fixtures():
    a,x,Y=s.symbols('a x Y',real=True,positive=True)
    assert s.expand(x*(2*s.sqrt(Y)*a-Y*x)-(a*a-(s.sqrt(Y)*x-a)**2))==0
    # Independent scalar quadrature and sign-crossing reference.
    err=0.; count=0
    for Y in (.01,1.,100.):
        for h in (.0001,.2,2.):
            for a in (np.array([0.,0.]),np.array([.4,-.3])):
                z=np.array([.2,-.7,1.]); v,I,F=port(z,slice(0,3),1.3,Y,a,h)
                al=Y/1.3; d=np.sqrt(al)*z[:2]-2*a
                ref=quad(lambda t:np.linalg.norm(a+d*np.exp(-al*t))**2,0,h,epsabs=1e-12)[0]
                err=max(err,abs(ref-F@F)); count+=1
    for p,q in ((-1,3),(3,-1),(1,2),(-2,-1),(0,0)):
        P,N=gross(p,q); assert abs(P-N-(p+q)/2)<1e-14
        assert abs(P-quad(lambda t:max(0,p+(q-p)*t),0,1)[0])<1e-10
    assert err<1e-10
    g=Grid(.8,[cell(1.,(1.,),(.3,),(-.5,)),cell(1.2,(.8,),(.4,),(1.,),.5)],1.); h=.15; n=18; m=IncidentGrid(g,h,[1.,.7])
    ports=np.zeros((g.size,6)); observe=np.zeros(g.size)
    for i,(sl,_,_) in enumerate(g.local): ports[sl.start:sl.start+3,3*i:3*i+3]=np.eye(3)
    observe[g.local[-1][0].start]=1.; L,B=lift(m,n,ports,observe); target=np.zeros(g.size+1); target[-1]=.12
    t=np.arange(n)*h; src=np.zeros((n,2,2)); src[:,0,0]=.4*np.sin(t); src[:,0,1]=.3*np.cos(t)
    out={}; rng=np.random.default_rng(369)
    for label,source in [('on',src),('off',src*0)]:
        rhs=target-L@source.ravel(); x=np.linalg.lstsq(B,rhs,rcond=1e-12)[0]; assert np.linalg.norm(B@x-rhs)<1e-9
        _,w0,_=m.run(source,ports,x,observe); u,w,Z,kkt=optimize(m,source,ports,observe,B,x,2.)
        endpoint,wr,_=m.run(source,ports,u,observe); assert np.linalg.norm(endpoint-target)<1e-9 and np.array_equal(w,wr)
        cap=h*np.sum(source**2); assert abs(w[0]-cap)<1e-12 and net(w,1,1,0)<=cap+1e-10
        for _ in range(20):
            d=rng.normal(size=Z.shape[1]); d*=2*rng.random()/np.linalg.norm(d); _,q,_=m.run(source,ports,x+Z@d,observe)
            assert net(q,1,1,0)<=net(w,1,1,0)+1e-9
        # Robust lower bound for THIS schedule over declared efficiency/cost box only.
        lower=net(w,.8,.5,.01); upper=net(w,1,1,0)
        for ei in (.8,.9,1.):
            for er in (.5,.75,1.):
                for aux in (0,.005,.01): assert lower-1e-12<=net(w,ei,er,aux)<=upper+1e-12
        if label=='off': assert upper<=1e-10
        out[label]={'incident':float(cap),'baseline_ideal_net':net(w0,1,1,0),'optimized_ideal_net':upper,'efficiency_box_worst_schedule_net':lower,'no_recovery_schedule_net':net(w,1,0,0),'ledger_order':['incident','outgoing','material','load','gross_controller_in','gross_controller_out'],'ledger':w.tolist(),'kkt_residual':float(kkt),'endpoint_residual':float(np.linalg.norm(endpoint-target))}
    return dict(status='CONDITIONAL_INCIDENT_PORT_AND_RECOVERY',physical_admission=False,port_quadrature_fixtures=count,max_quadrature_error=err,gross_sign_fixtures=5,endpoint_rank=int(np.linalg.matrix_rank(B)),comparison_fixtures=40,cases=out,scope='Synthetic matched real-admittance ports, fixed incident trace, fixed material and full numerical return. Efficiency box is a trial cost model, not measured hardware or robust physical source uncertainty. Ideal net optimized; nonideal values evaluate that schedule, not a global nonideal optimum.')

if __name__=='__main__': print(json.dumps(fixtures(),indent=2))
