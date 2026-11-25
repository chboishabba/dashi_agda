"""P0S: finite six-face reservoirs and time-indexed conformal metric.
Reuse P0Q native incidence and original SG/kinetics; P0R matched midpoint.
Prescribed homogeneous spatial scale, not Einstein evolution or exterior radiation.
Synthetic material parameters; no authentic BH4 calibration.
"""
import numpy as np
from scipy.optimize import root
from hopf369_maxwell_pnp import G,C,L,R,base,drive,metrics
import hopf369_midpoint_pnp as mid

# Same exterior half-edge order as P0Q; each ends in its actual face reservoir.
outer=[]; faces=[]
for i,p in enumerate(base.POINTS):
    for axis in range(3):
        for sign in (-1,1):
            if p[axis]+sign not in (-1,0,1):
                outer.append(i); faces.append(2*axis+(sign==1))
left=np.r_[L,outer]; right=np.r_[R,27+np.array(faces)]
H=np.zeros((33,108),dtype=int)
H[left,np.arange(108)]=-1; H[right,np.arange(108)]=1
assert np.array_equal(H[:27],G) and np.all(np.bincount(faces)==9)
assert not np.any(H@C.T) and not np.any(H.sum(axis=0))

def geometry(m,scale,mu=1.):
    if not np.isfinite(scale) or scale<=0: raise ValueError('positive spatial scale required')
    M,N=metrics(m,mu)
    return 1/(scale*M),N/scale,m.h**3*scale**3*np.r_[np.ones(27),9*np.ones(6)]

def charge(n,m):
    return m.F*(n@m.z)
def interior_charge(n,m,V):
    # Fixed background amount per original voxel: no unaccounted new charge on expansion.
    return charge(n[:27],m)+m.h**3*m.fixed_charge

def chem(n,V,m):
    return float(np.sum(n*(m.standard_mu+m.RT*(np.log(n/V[:,None])-1))))

def total(n,d,b,K,N,V,m):
    return chem(n,V,m)+.5*(d@(K*d)+b@(N*b))

def initial(c,m,scale=1.,amplitude=1.,electric=.3,mu=1.):
    K,N,V=geometry(m,scale,mu);n=c*V[:,None]
    a=np.r_[drive.hopf_cochain(),np.zeros(54)]
    A=(G/K)@G.T; phi=np.linalg.solve(A,interior_charge(n,m,V))
    et=a-G.T@np.linalg.solve(A,G@(a/K))
    d=(-G.T@phi+electric*et)/K
    return n,d,amplitude*(C@a),np.zeros(33)

def step(n0,d0,b0,q0,dt,m,scale0,scale1,permeability=1.,source=None,mu=1.,tol=1e-9):
    n0,d0,b0,q0=map(lambda x:np.asarray(x,float),(n0,d0,b0,q0))
    s=np.zeros(108) if source is None else np.asarray(source,float)
    if n0.shape!=(33,len(m.z)) or d0.shape!=(108,) or b0.shape!=(36,) or q0.shape!=(33,) or s.shape!=(108,) or not all(np.all(np.isfinite(v)) for v in (n0,d0,b0,q0,s)) or np.any(n0<=0) or not np.isfinite(dt) or dt<=0 or not np.isfinite(permeability) or permeability<0: raise ValueError('invalid source state')
    K0,N0,V0=geometry(m,scale0,mu); K1,N1,V1=geometry(m,scale1,mu)
    K=(K0+K1)/2; N=(N0+N1)/2
    g0=-G@d0-interior_charge(n0,m,V0)-q0[:27]
    if np.max(abs(g0))>tol: raise ValueError('initial Gauss unpaid')
    q1=q0-dt*H@s
    # Physical area/length of uniform conformal cell; endpoint SG on amounts.
    conductance=m.h*scale1*np.r_[np.ones(54),2*permeability*np.ones(54)]
    def terms(n,v):
        c=n/V1[:,None]; u=-v[:,None]*m.z*m.F/m.RT
        a=c[left]*base.bernoulli(u); b=c[right]*base.bernoulli(-u)
        J=conductance[:,None]*m.D*(a-b) # mol/s, not flux density
        rates=base.reaction_rates(c[:27],m)
        f=H@J; f[:27]+=V1[:27,None]*(rates@(m.products-m.reactants))
        return f,m.F*(J@m.z),a,b,J,rates
    size=n0.size
    def unpack(y):
        n=np.exp(np.clip(y[:size].reshape(n0.shape),-60,60));v=y[size:]
        return n,v,2*v/K-d0,b0-dt*C@v
    def residual(y):
        n,v,d,b=unpack(y); f,j,*_=terms(n,v)
        return np.r_[(n-n0-dt*f).ravel(),d-d0-dt*(C.T@(N*(b+b0)/2)-j+s)]
    sol=root(residual,np.r_[np.log(n0).ravel(),K*d0],options={'xtol':1e-10})
    if not np.all(np.isfinite(sol.x)) or np.any(abs(sol.x[:size])>=59): raise RuntimeError('invalid root')
    n,v,d,b=unpack(sol.x); f,j,a,y,J,rates=terms(n,v)
    rn=n-n0-dt*f; rd=d-d0-dt*(C.T@(N*(b+b0)/2)-j+s)
    err=max(np.max(abs(rn)),np.max(abs(rd)))
    if not np.isfinite(err) or err>tol or np.any(a<=0) or np.any(y<=0): raise RuntimeError('unpaid root')
    cm=m.standard_mu+m.RT*np.log(n/V1[:,None])
    Dt=dt*m.RT*float(np.sum(J*(np.log(a)-np.log(y))))
    Dr=-dt*float(np.sum(V1[:27,None]*rates*(cm[:27]@(m.products-m.reactants).T)))
    Bc=m.RT*float(np.sum(n0*np.log(n0/n)-n0+n))
    We=.25*float((K1-K0)@(d*d+d0*d0)); Wb=.25*float((N1-N0)@(b*b+b0*b0))
    Wv=-m.RT*float(np.sum(n0*np.log(V1/V0)[:,None]))
    Ws=dt*float(v@s); transfer=dt*float(v@j); numerical=float(np.sum(cm*rn)+v@rd)
    delta=total(n,d,b,K1,N1,V1,m)-total(n0,d0,b0,K0,N0,V0,m)
    closure=delta-Ws-We-Wb-Wv+Dt+Dr+Bc-numerical
    field_delta=.5*(d@(K1*d)+b@(N1*b)-d0@(K0*d0)-b0@(N0*b0))
    field_closure=field_delta-Ws-We-Wb+transfer-v@rd
    g1=-G@d-interior_charge(n,m,V1)-q1[:27]
    gauss=float(np.max(abs(g1))); prop=float(np.max(abs(g1-g0+G@rd+m.F*(rn[:27]@m.z))))
    face_amount=dt*(H[27:]@J); face_charge=face_amount@m.z*m.F
    exchange=float(np.max(abs(n[27:]-n0[27:]-face_amount-rn[27:])))
    charge_defect=float(abs(np.sum(charge(n,m)-charge(n0,m))))
    source_charge_defect=float(abs(np.sum(q1-q0)))
    A=(G/K1)@G.T; Q=interior_charge(n,m,V1)+q1[:27]
    phi=np.linalg.solve(A,Q); et=K1*d+G.T@phi
    split=float(abs(.5*d@(K1*d)-.5*Q@phi-.5*et@(et/K1)))
    values=[closure,field_closure,gauss,prop,exchange,charge_defect,source_charge_defect,split,Dt,Dr,Bc,delta,numerical,We,Wb,Wv,Ws,transfer]
    if not np.all(np.isfinite(values)) or min(Dt,Dr,Bc)<-1e-9 or max(abs(closure),abs(field_closure),gauss,prop,exchange,charge_defect,source_charge_defect,split)>1e-8: raise RuntimeError('unpaid coupled ledger')
    return n,d,b,q1,dict(residual=float(err),minimum=float(np.min(n/V1[:,None])),closure=float(closure),field_closure=float(field_closure),gauss=gauss,propagation=prop,exchange=exchange,charge_defect=charge_defect,source_charge_defect=source_charge_defect,split=split,delta=float(delta),source_work=Ws,electric_metric_work=We,magnetic_metric_work=Wb,volume_work=Wv,transport_loss=Dt,reaction_loss=Dr,chemical_remainder=Bc,numerical_work=numerical,transfer=transfer,face_amount=face_amount.tolist(),face_charge=face_charge.tolist())

def assay():
    import sympy as sp
    # Exact algebraic discrete-gradient identity for each storage coordinate.
    x,y,k,l=sp.symbols('x y k l'); half=sp.Rational(1,2)
    assert sp.expand(half*(l*y*y-k*x*x)-(k+l)*(x+y)*(y-x)/4-(l-k)*(x*x+y*y)/4)==0
    assert sp.Matrix(H).rank()==32 and sp.Matrix(C).rank()==28
    rec=[]; parity=[]
    for ns in (3,29):
        if ns==3:
            A=np.array([[1,1,0]]);B=np.array([[0,0,1]]);z=np.array([1,-1,0]);w=np.array([[1,0],[0,1],[1,1]])
        else:
            A=np.eye(ns,dtype=int)[0:24:2];B=np.eye(ns,dtype=int)[1:24:2];z=np.repeat(np.arange(15)%3-1,2)[:ns];w=np.repeat(np.eye(15),2,axis=0)[:ns]
        m=base.Model(z=z,D=np.linspace(.08,.12,ns),reactants=A,products=B,kf=np.full(len(A),.04),kb=np.full(len(A),.04),standard_mu=np.zeros(ns))
        c=1+.15*np.sin(np.arange(33*ns).reshape(33,ns));n,d,b,q=initial(c,m)
        # Fixed metric, blocked exterior must reproduce P0R on interior and full field.
        K,N,V=geometry(m,1.); cp,ep,bp,_=mid.step(c[:27],K*d,b,.08,m)
        nn,dd,bb,qq,r=step(n,d,b,q,.08,m,1.,1.,0.)
        parity.append(max(np.max(abs(cp-nn[:27]/V[:27,None])),np.max(abs(ep-K*dd)),np.max(abs(bp-bb))))
        assert parity[-1]<1e-9 and np.max(abs(nn[27:]-n[27:]))<1e-10
        for amp in (1.,-1.):
            n,d,b,q=initial(c,m,amplitude=amp,electric=.3*amp); inv=n.sum(axis=0)@w
            for t,(a0,a1) in enumerate(((1.,1.),(1.,1.08),(1.08,.94),( .94,1.))):
                s=np.zeros(108)
                if t==1:s[54]=.2 # explicitly charged source, not projected away
                n,d,b,q,r=step(n,d,b,q,.08,m,a0,a1,1.,s)
                assert np.max(abs(n.sum(axis=0)@w-inv))<1e-8
                rec.append(dict(species=ns,amplitude=amp,time=t,scale0=a0,scale1=a1,**r))
    return dict(steps=rec,blocked_parity=parity,exact_incidence_rank=32,exact_curl_rank=28)

if __name__=='__main__':
    import json
    print(json.dumps(assay(),indent=2))
