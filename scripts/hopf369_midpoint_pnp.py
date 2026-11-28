"""P0R: midpoint Maxwell, positive endpoint SG/reaction coupling.
Reuse P0Q geometry/metrics and P0P flux; not a full second-order material
scheme, calibrated BH4, exterior radiation model, or kernel proof.
"""
import numpy as np
from scipy.optimize import root
import hopf369_maxwell_pnp as q
from hopf369_maxwell_pnp import G,C,L,R,base,drive


def step(c0,e0,b0,dt,m,source=None,mu=1.,tol=1e-9):
    c0=np.asarray(c0,float); e0=np.asarray(e0,float); b0=np.asarray(b0,float)
    s=np.zeros(108) if source is None else np.asarray(source,float)
    if c0.shape!=(27,len(m.z)) or e0.shape!=(108,) or b0.shape!=(36,) or s.shape!=(108,) or not all(np.all(np.isfinite(v)) for v in (c0,e0,b0,s)) or np.any(c0<=0) or not np.isfinite(dt) or dt<=0:
        raise ValueError('invalid state or step')
    M,N=q.metrics(m,mu)
    g0=-G@(M*e0)-q.charge(c0,m)
    if np.max(abs(g0))>tol or np.max(abs(G@s))>tol:
        raise ValueError('initial Gauss or external charge continuity unpaid')
    n=c0.size
    def terms(c,v):
        # P0P SG with exact total midpoint voltage; no double counted Poisson.
        p=base.poisson(c,m)
        a,b,J=drive.flux_parts(c,p,m,v[:54]+p[R]-p[L])
        f=np.zeros_like(c); np.add.at(f,L,-J/m.h); np.add.at(f,R,J/m.h)
        rates=base.reaction_rates(c,m); f+=rates@(m.products-m.reactants)
        j=np.r_[m.h**2*m.F*(J@m.z),np.zeros(54)]
        return f,j,a,b,J,rates
    def residual(y):
        c=np.exp(np.clip(y[:n].reshape(c0.shape),-60,60)); v=y[n:]
        f,j,*_=terms(c,v)
        return np.r_[(c-c0-dt*f).ravel(),2*M*(v-e0)-dt*(C.T@(N*(b0-dt/2*C@v))-j+s)]
    sol=root(residual,np.r_[np.log(c0).ravel(),e0],options={'xtol':1e-10})
    if not np.all(np.isfinite(sol.x)) or np.any(abs(sol.x[:n])>=59): raise RuntimeError('invalid implicit log root')
    c=np.exp(sol.x[:n].reshape(c0.shape)); v=sol.x[n:]; e=2*v-e0; b=b0-dt*C@v
    f,j,a,d,J,rates=terms(c,v)
    rc=c-c0-dt*f; re=M*(e-e0)-dt*(C.T@(N*((b+b0)/2))-j+s)
    err=max(np.max(abs(rc)),np.max(abs(re)))
    if not np.isfinite(err) or err>tol or np.any(a<=0) or np.any(d<=0): raise RuntimeError('unpaid root/SG branches')
    chem_mu=m.standard_mu+m.RT*np.log(c)
    Dt=m.h**2*m.RT*float(np.sum(J*(np.log(a)-np.log(d))))
    Dr=-m.h**3*float(np.sum(rates*(chem_mu@(m.products-m.reactants).T)))
    W=dt*float(v@s); transfer=dt*float(v@j)
    Bc=m.h**3*m.RT*float(np.sum(c0*np.log(c0/c)-c0+c))
    rn=m.h**3*float(np.sum(chem_mu*rc))+float(v@re)
    delta=q.energy(c,e,b,m,M,N)-q.energy(c0,e0,b0,m,M,N)
    closure=delta-W+dt*(Dt+Dr)+Bc-rn
    field_delta=.5*(e@(M*e)+b@(N*b)-e0@(M*e0)-b0@(N*b0))
    field_closure=field_delta-W+transfer-float(v@re)
    g=-G@(M*e)-q.charge(c,m)
    gauss=float(np.max(abs(g)))
    propagation=float(np.max(abs(g-g0+G@re+m.h**3*m.F*(rc@m.z))))
    p=base.poisson(c,m); et=e+G.T@p
    split=abs(.5*e@(M*e)-(.5*et@(M*et)+.5*q.charge(c,m)@p))
    vals=[err,Dt,Dr,W,transfer,Bc,rn,delta,closure,field_closure,gauss,propagation,split]
    if not np.all(np.isfinite(vals)) or min(Dt,Dr,Bc)<-tol or max(abs(closure),abs(field_closure),gauss,propagation,split)>1e-8: raise RuntimeError('unpaid midpoint ledger')
    return c,e,b,dict(residual=float(err),gauss=gauss,propagation=propagation,split=float(split),closure=float(closure),field_closure=float(field_closure),minimum=float(c.min()),work=W,transfer=transfer,delta=float(delta),transport_loss=dt*Dt,reaction_loss=dt*Dr,chemical_remainder=Bc,electric_remainder=0.,magnetic_remainder=0.,numerical_work=rn)


def assay():
    import sympy as sp
    # Reuse the identical P0Q assay, changing ONLY the stepping operator.
    old=q.step
    try:
        q.step=step
        receipt=q.assay()
    finally: q.step=old
    # Exact rational Cayley identity on a weighted curl primitive.
    a,m,n,t=sp.symbols('a m n t',positive=True)
    A=sp.Matrix([[0,a*n/m],[-a,0]]); H=sp.diag(m,n); I=sp.eye(2)
    T=(I-t*A/2).inv()*(I+t*A/2)
    assert (T.T*H*T-H).applyfunc(sp.factor)==sp.zeros(2)
    assert (T.subs(t,-t)*T-I).applyfunc(sp.factor)==sp.zeros(2)
    # Full carrier vacuum/frozen-ion comparison; both field zero sectors nonzero.
    m=base.Model(z=np.array([1,-1]),D=np.zeros(2),reactants=np.zeros((0,2),int),products=np.zeros((0,2),int),kf=np.zeros(0),kb=np.zeros(0),standard_mu=np.zeros(2))
    c=np.ones((27,2)); M,N=q.metrics(m,1.)
    e,b=q.initial(c,m,amplitude=1.,electric=.3)
    # Two exterior edges of same corner: exact divergence/curl-free voltage.
    ext=np.flatnonzero(G[0,54:])+54
    z=np.zeros(108); z[ext[0]]=1; z[ext[1]]=-1
    assert not np.any(C@z) and not np.any(G@(M*z))
    # Incompatible magnetic constraint payload retained for diagnostic only.
    w=np.array(sp.Matrix(C.T).nullspace()[0],dtype=float).ravel()
    assert not np.any(C.T@(N*w))
    e=e+.2*z; b=b+.1*w
    e0=e.copy(); b0=b.copy(); U0=q.energy(c,e,b,m,M,N)
    be=old(c,e,b,.08,m)[3]; mp=step(c,e,b,.08,m)[3]
    records=[]
    for dt in (.08,.4,1.,.08):
        c,e,b,r=step(c,e,b,dt,m)
        records.append(r)
        assert abs(q.energy(c,e,b,m,M,N)-U0)<1e-9
        assert abs(z@(M*(e-e0)))<1e-10 and abs(w@(N*(b-b0)))<1e-10
    # Inverse Cayley step in frozen sector, using algebraic negative-dt update
    # (not a negative material timestep).
    dt=.08
    K=2*np.diag(M)+dt**2/2*(C.T*N)@C
    v=np.linalg.solve(K,2*M*e0+dt*C.T@(N*b0)); e1=2*v-e0; b1=b0-dt*C@v
    vr=np.linalg.solve(K,2*M*e1-dt*C.T@(N*b1)); er=2*vr-e1; br=b1+dt*C@vr
    reverse=max(np.max(abs(er-e0)),np.max(abs(br-b0)))
    assert reverse<1e-12
    assert be['delta']<-.01 and abs(mp['delta'])<1e-9
    receipt.update(vacuum_steps=records,backward_euler_frozen=be,midpoint_frozen=mp,reverse_error=float(reverse),exact_cayley_checks=2)
    return receipt

if __name__=='__main__':
    import json
    print(json.dumps(assay(),indent=2))
