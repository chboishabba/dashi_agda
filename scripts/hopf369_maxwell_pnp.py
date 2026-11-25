"""P0Q finite Maxwell/PNP feedback, original 54 interior bonds.
54 grounded half-edges close the original Poisson Gauss law; no exterior
magnetic plaquettes or radiative continuum claim. All test parameters synthetic.
"""
import numpy as np
from scipy.optimize import root
from itertools import combinations, product
import reactive_pnp_369 as base
import hopf369_driven_pnp as drive

L,R=np.array(base.BONDS).T
G=np.zeros((27,108),dtype=int)
G[L,np.arange(54)]=-1; G[R,np.arange(54)]=1
k=54
for i,p in enumerate(base.POINTS):
    for axis in range(3):
        for sign in (-1,1):
            if p[axis]+sign not in (-1,0,1):
                G[i,k]=-1; k+=1
assert k==108
C=np.zeros((36,108),dtype=int)
row=0
for i,j in combinations(range(3),2):
    for a,b,t in product((-1,0),(-1,0),(-1,0,1)):
        p=[t]*3;p[i]=a;p[j]=b
        q=p.copy();q[i]+=1; r=p.copy();r[j]+=1;s=q.copy();s[j]+=1
        for x,y,sgn in ((p,q,1),(q,s,1),(r,s,-1),(p,r,-1)):
            C[row,base.BONDS.index((base.INDEX[tuple(x)],base.INDEX[tuple(y)]))]=sgn
        row+=1
assert row==36 and not np.any(C@G.T)

def metrics(m,mu):
    if not np.isfinite(mu) or mu<=0: raise ValueError('positive permeability required')
    M=m.epsilon*m.h*np.r_[np.ones(54),2*np.ones(54)]
    N=np.full(36,1/(mu*m.h))
    return M,N

def project(e,M):
    return e-G.T@np.linalg.solve((G*M)@G.T,G@(M*e))

def charge(c,m): return m.h**3*(m.F*(c@m.z)+m.fixed_charge)
def chemical(c,m): return m.h**3*float(np.sum(m.RT*c*(np.log(c)-1)+c*m.standard_mu))
def energy(c,e,b,m,M,N): return chemical(c,m)+.5*(e@(M*e)+b@(N*b))

def initial(c,m,amplitude=1.,electric=0.,mu=1.):
    M,N=metrics(m,mu); a=np.r_[drive.hopf_cochain(),np.zeros(54)]
    e=-G.T@base.poisson(c,m)+electric*project(a,M)
    return e,amplitude*(C@a)

def step(c0,e0,b0,dt,m,source=None,mu=1.,tol=1e-9):
    c0=np.asarray(c0,float);e0=np.asarray(e0,float);b0=np.asarray(b0,float)
    s=np.zeros(108) if source is None else np.asarray(source,float)
    if c0.shape!=(27,len(m.z)) or e0.shape!=(108,) or b0.shape!=(36,) or s.shape!=(108,) or not all(np.all(np.isfinite(v)) for v in (c0,e0,b0,s)) or np.any(c0<=0) or not np.isfinite(dt) or dt<=0: raise ValueError('invalid initial state or step')
    M,N=metrics(m,mu)
    if np.max(abs(-G@(M*e0)-charge(c0,m)))>tol or np.max(abs(G@s))>tol: raise ValueError('initial Gauss or external charge continuity unpaid')
    n=c0.size
    def terms(c,e):
        # Same P0P flux, with total electric voltage on the original bonds.
        p=base.poisson(c,m); v=e[:54]+p[R]-p[L]
        a,b,J=drive.flux_parts(c,p,m,v)
        f=np.zeros_like(c);np.add.at(f,L,-J/m.h);np.add.at(f,R,J/m.h)
        rates=base.reaction_rates(c,m);f+=rates@(m.products-m.reactants)
        j=np.r_[m.h**2*m.F*(J@m.z),np.zeros(54)]
        return f,j,a,b,J,rates
    def residual(y):
        c=np.exp(np.clip(y[:n].reshape(c0.shape),-60,60));e=y[n:];b=b0-dt*C@e
        f,j,*_=terms(c,e)
        return np.r_[(c-c0-dt*f).ravel(),M*(e-e0)-dt*(C.T@(N*b)-j+s)]
    sol=root(residual,np.r_[np.log(c0).ravel(),e0],options={'xtol':1e-10})
    if not np.all(np.isfinite(sol.x)) or np.any(abs(sol.x[:n])>=59): raise RuntimeError('invalid implicit root')
    c=np.exp(sol.x[:n].reshape(c0.shape));e=sol.x[n:];b=b0-dt*C@e
    f,j,a,d,J,rates=terms(c,e)
    rc=c-c0-dt*f; re=M*(e-e0)-dt*(C.T@(N*b)-j+s)
    err=max(np.max(abs(rc)),np.max(abs(re)))
    if np.any(a<=0) or np.any(d<=0) or err>tol: raise RuntimeError('unpaid root/SG branches')
    chem_mu=m.standard_mu+m.RT*np.log(c)
    Dt=m.h**2*m.RT*float(np.sum(J*(np.log(a)-np.log(d))))
    Dr=-m.h**3*float(np.sum(rates*(chem_mu@(m.products-m.reactants).T)))
    W=dt*float(e@s); transfer=dt*float(e@j)
    Bc=m.h**3*m.RT*float(np.sum(c0*np.log(c0/c)-c0+c))
    Be=.5*float((e-e0)@(M*(e-e0))); Bb=.5*float((b-b0)@(N*(b-b0)))
    rn=m.h**3*float(np.sum(chem_mu*rc))+float(e@re)
    delta=energy(c,e,b,m,M,N)-energy(c0,e0,b0,m,M,N)
    closure=delta-W+dt*(Dt+Dr)+Bc+Be+Bb-rn
    gauss=float(np.max(abs(-G@(M*e)-charge(c,m))))
    p=base.poisson(c,m); et=e+G.T@p
    split=abs(.5*e@(M*e)-(.5*et@(M*et)+.5*charge(c,m)@p))
    vals=[err,Dt,Dr,W,transfer,Bc,Be,Bb,rn,delta,closure,gauss,split]
    if not np.all(np.isfinite(vals)) or min(Dt,Dr,Bc,Be,Bb)<-tol or abs(closure)>1e-8 or gauss>1e-8 or split>1e-8: raise RuntimeError('unpaid energy/Gauss ledger')
    return c,e,b,dict(residual=float(err),gauss=gauss,split=float(split),closure=float(closure),minimum=float(c.min()),work=W,transfer=transfer,delta=float(delta),transport_loss=dt*Dt,reaction_loss=dt*Dr,chemical_remainder=Bc,electric_remainder=Be,magnetic_remainder=Bb,numerical_work=rn)

def assay():
    import sympy as sp
    M0=np.r_[np.ones(54,dtype=int),2*np.ones(54,dtype=int)]
    assert np.array_equal((G*M0)@G.T,base.poisson_matrix(1))
    ranks=(sp.Matrix(G).rank(),sp.Matrix(C).rank())
    assert ranks==(27,28)
    records=[]
    for n in (3,29):
        if n==3:
            A=np.array([[1,1,0]]);B=np.array([[0,0,1]]);z=np.array([1,-1,0]);weights=np.array([[1,0],[0,1],[1,1]])
        else:
            A=np.eye(n,dtype=int)[0:24:2];B=np.eye(n,dtype=int)[1:24:2];z=np.repeat(np.arange(15)%3-1,2)[:n];weights=np.repeat(np.eye(15),2,axis=0)[:n]
        m=base.Model(z=z,D=np.linspace(.08,.12,n),reactants=A,products=B,kf=np.full(len(A),.04),kb=np.full(len(A),.04),standard_mu=np.zeros(n))
        c0=1+.15*np.sin(np.arange(27*n).reshape(27,n));M,N=metrics(m,1.)
        a=np.r_[drive.hopf_cochain(),np.zeros(54)];s=C.T@(C@a)
        for amp in (0.,1.,-1.):
            c=c0.copy();e,b=initial(c,m,amplitude=amp,electric=.2*amp)
            bstart=b.copy()
            for t in range(3):
                src=.3*s if t==1 else np.zeros(108)
                c,e,b,r=step(c,e,b,.08,m,src)
                np.testing.assert_allclose((c-c0).sum(axis=0)@weights,0,atol=1e-8)
                # Eight left-kernel magnetic residuals retained, not reset.
                np.testing.assert_allclose(b-bstart,C@np.linalg.lstsq(C,b-bstart,rcond=None)[0],atol=1e-10)
                if t!=1: assert r['delta']<=1e-9
                records.append(dict(species=n,amplitude=amp,time=t,**r))
    # Same-field backreaction: diffusion 0 and positive mobility from neutral pair.
    n=2;c0=np.ones((27,n)); kw=dict(z=np.array([1,-1]),reactants=np.zeros((0,2),int),products=np.zeros((0,2),int),kf=np.zeros(0),kb=np.zeros(0),standard_mu=np.zeros(2))
    mobile=base.Model(D=np.ones(2)*.1,**kw); frozen=base.Model(D=np.zeros(2),**kw)
    e,b=initial(c0,mobile,amplitude=1.,electric=.3)
    _,em,bm,rm=step(c0,e,b,.08,mobile);_,ef,bf,rf=step(c0,e,b,.08,frozen)
    diff=float(np.linalg.norm(em-ef));assert diff>1e-6 and rm['transfer']>0 and abs(rf['transfer'])<1e-12
    # Nonconservative source rejected rather than silently projecting it.
    try: step(c0,e,b,.08,mobile,np.ones(108))
    except ValueError: pass
    else: raise AssertionError('unpaid external charge accepted')
    return dict(ranks=ranks,steps=records,backreaction_field_difference=diff,mobile=rm,frozen=rf)

if __name__=='__main__':
    import json
    print(json.dumps(assay(),indent=2))
