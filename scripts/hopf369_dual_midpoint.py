"""P0Z: P0Y exact dual maps + curved cubical midpoint receiver.
Selected passive boundary load; not a full exterior Maxwell or brane solve.
Synthetic kinetics only in assay; source adapter remains fail-closed.
"""
import numpy as np
from itertools import product, combinations
from scipy.integrate import solve_ivp, quad
from scipy.optimize import root
from scipy.special import exprel
from numpy.polynomial.legendre import leggauss
import check_hopf369_p0y as y

G,J,E,Q,V=(np.array(a,float) for a in (y.G,y.J,y.E,y.Q,y.V))
Rface,Sface=(np.array(a,float) for a in (y.Rface,y.S))
P=y.P; edges=y.edges; flux=y.flux
faces=[]
for i,j in combinations(range(3),2):
    k=3-i-j
    for a,b,c in product(range(2),range(2),range(3)):
        p=[c]*3;p[i]=a;p[j]=b;faces.append((i,j,tuple(p)))
def shift(p,i):
    q=list(p);q[i]+=1;return tuple(q)
C=np.zeros((36,54));Z=np.zeros((8,36));cells=list(product(range(2),repeat=3))
for l,(i,j,p) in enumerate(faces):
    for k,q,sgn in ((i,p,1),(j,shift(p,i),1),(i,shift(p,j),-1),(j,p,-1)):C[l,edges.index((k,q))]=sgn
for l,p in enumerate(cells):
    for k in range(3):
        i,j=[a for a in range(3) if a!=k];sgn=(-1)**k
        Z[l,faces.index((i,j,p))]=-sgn;Z[l,faces.index((i,j,shift(p,k)))]=sgn
assert not np.any(C@G.T) and not np.any(Z@C)
Vhat=np.zeros((33,108));Vhat[:27]=V
boundary=[[] for _ in range(6)]
for l,(a,p) in enumerate(flux):
    if p[a] in (0,3):
        f=2*a+int(p[a]==3);Vhat[27+f,l]=1;boundary[f].append(l)
left=np.argmax(Vhat==-1,axis=0);right=np.argmax(Vhat==1,axis=0)
assert np.all((Vhat==-1).sum(axis=0)==1) and np.all((Vhat==1).sum(axis=0)==1)

def basis(p,x):
    e=np.zeros((3,54));b=np.zeros((3,36))
    for l,(i,q) in enumerate(edges):
        d=np.array(q)-p
        if d[i]==0 and all(d[j] in (0,1) for j in range(3)):
            e[i,l]=np.prod([x[j] if d[j] else 1-x[j] for j in range(3) if j!=i])
    for l,(i,j,q) in enumerate(faces):
        k=3-i-j;d=np.array(q)-p
        if d[i]==d[j]==0 and d[k] in (0,1):b[k,l]=(-1)**k*(x[k] if d[k] else 1-x[k])
    return e,b

def A(x):
    x,y,z=x;D=1+x*x+y*y+z*z;return 2*np.array([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2

def geometry(eps=.25,order=5):
    """P0W initial graph geometry, radial original KK constraint, numerical quadrature."""
    sol=solve_ivp(lambda r,u:[u[1],-eps**2*64/(12*(1+r*r)**4)*u[0]],(0,64),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
    normal=sol.y[1,-1]
    def g(x):
        r=np.linalg.norm(x);psi=(sol.sol(r)[0]/r if r else 1)/normal;a=eps*A(x)
        return psi**2*(np.eye(3)+np.outer(a,a))
    t,w=leggauss(order);t=(t+1)/2;w=w/2;M=np.zeros((54,54));N=np.zeros((36,36));vol=np.zeros(33);Pport=np.zeros((54,48));col=0
    for p in cells:
        for ijk in product(range(order),repeat=3):
            x=t[list(ijk)];e,b=basis(p,x);h=g(np.array(p)+x-1);det=np.sqrt(np.linalg.det(h));weight=np.prod(w[list(ijk)])
            M+=weight*e.T@(det*np.linalg.inv(h))@e;N+=weight*b.T@(h/det)@b
        for k in range(3):
            for side in (0,1):
                if p[k]+side not in (0,2):continue
                ij=[i for i in range(3) if i!=k];normalvec=np.eye(3)[k]*(2*side-1)
                for u,v in product(range(order),repeat=2):
                    x=np.zeros(3);x[k]=side;x[ij]=[t[u],t[v]];e,_=basis(p,x)
                    Pport[:,col:col+2]+=w[u]*w[v]*np.cross(normalvec,e.T)[:,ij]
                col+=2
    assert col==48
    assert np.max(abs((G@Pport)[P.index((1,1,1))]))<1e-12
    bounds=[(-1,-.5),(-.5,.5),(.5,1)]
    for i,p in enumerate(P):
        lo=np.array([bounds[k][0] for k in p]);width=np.array([bounds[k][1]-bounds[k][0] for k in p])
        for ijk in product(range(order),repeat=3):
            vol[i]+=np.prod(w[list(ijk)]*width)*np.sqrt(np.linalg.det(g(lo+width*t[list(ijk)])))
    # Explicit selected reservoir volumes (not biological measurements).
    vol[27:]=4
    a=np.array([eps*quad(lambda u:A(np.array(p)-1+np.eye(3)[i]*u)[i],0,1,epsabs=1e-12)[0] for i,p in edges])
    return np.linalg.inv(M),N,vol,Pport,a

def scaled(geom,a):
    K,N,V,Pport,seed=geom
    return K/a,N/a,V*a**3,Pport,seed

def bern(u):
    return 1/exprel(u)

def step(n0,d0,b0,q0,l0,dt,model,g0,g1,conductance,drive=None,loss=.2,tol=1e-9):
    z,RT,F,mu,A0,A1,kf,kb=model
    K0,N0,V0,Pport,_=g0;K1,N1,V1,P1,_=g1
    if not np.array_equal(Pport,P1):raise ValueError('common chart port required')
    n0,d0,b0,q0,l0=map(lambda a:np.asarray(a,float),(n0,d0,b0,q0,l0))
    s=np.zeros(48) if drive is None else np.asarray(drive,float)
    k=np.asarray(conductance,float);ns=len(z)
    if n0.shape!=(33,ns) or d0.shape!=(54,) or b0.shape!=(36,) or q0.shape!=(27,) or l0.shape!=(48,) or k.shape!=(108,ns) or s.shape!=(48,) or not all(np.all(np.isfinite(a)) for a in (n0,d0,b0,q0,l0,k,s)) or np.any(n0<=0) or np.any(k<0) or not np.isfinite(dt) or dt<=0 or not np.isfinite(loss) or loss<0:raise ValueError('invalid state')
    nu=A1-A0
    if np.any(nu@z!=0):raise ValueError('reaction charge not conserved')
    if np.max(abs(RT*np.log(kf/kb)+nu@mu),initial=0)>1e-10:raise ValueError('detailed balance unpaid')
    for K,N,V in ((K0,N0,V0),(K1,N1,V1)):
        if not all(np.all(np.isfinite(a)) for a in (K,N,V)) or not np.allclose(K,K.T) or not np.allclose(N,N.T) or min(np.linalg.eigvalsh(K))<=0 or min(np.linalg.eigvalsh(N))<=0 or min(V)<=0:raise ValueError('positive metric and volumes required')
    if abs(q0[P.index((1,1,1))])>tol or np.max(abs(-G@d0-Q@(F*(n0[:27]@z))+q0))>tol:raise ValueError('initial boundary trace or Gauss unpaid')
    K=(K0+K1)/2;N=(N0+N1)/2;Ki=np.linalg.inv(K);size=n0.size
    def energy(n,d,b,l,K,N,V):return float(np.sum(n*(mu+RT*(np.log(n/V[:,None])-1)))+.5*(d@K@d+b@N@b+l@l))
    def unpack(u):
        n=np.exp(np.clip(u[:size].reshape(n0.shape),-60,60));v=u[size:];d=2*Ki@v-d0;b=b0-dt*C@v
        # Midpoint passive exterior trace load: ldot=P^T v - loss*lbar + s.
        lm=(l0+dt/2*(Pport.T@v+s))/(1+dt*loss/2);l=2*lm-l0
        return n,v,d,b,l,lm
    def terms(n,v):
        c=n/V1[:,None];voltage=J.T@v;xi=voltage[:,None]*F*z/RT
        a=c[left]*bern(-xi);b=c[right]*bern(xi);mol=k*(a-b);i=F*(mol@z)
        # Original gross sides, mass action; no fabricated original rate authority.
        lc=np.log(c[:27]);rates=np.exp(lc@A0.T)*kf-np.exp(lc@A1.T)*kb
        f=Vhat@mol;f[:27]+=V1[:27,None]*(rates@nu)
        return f,i,a,b,mol,rates
    def residual(u):
        n,v,d,b,l,lm=unpack(u);f,i,*_=terms(n,v)
        return np.r_[(n-n0-dt*f).ravel(),d-d0-dt*(C.T@N@((b+b0)/2)-J@i-Pport@lm)]
    sol=root(residual,np.r_[np.log(n0).ravel(),K@d0],options={'xtol':1e-10})
    if not np.all(np.isfinite(sol.x)) or np.any(abs(sol.x[:size])>=59):raise RuntimeError('invalid root')
    n,v,d,b,l,lm=unpack(sol.x);f,i,a,bgross,mol,rates=terms(n,v);p=Pport@lm
    rn=n-n0-dt*f;rd=d-d0-dt*(C.T@N@((b+b0)/2)-J@i-p)
    err=max(np.max(abs(rn)),np.max(abs(rd)))
    if err>tol or not np.isfinite(err) or np.any(a<=0) or np.any(bgross<=0):raise RuntimeError('unpaid root')
    q=q0-dt*(G@p+E@i);gstart=-G@d0-Q@(F*(n0[:27]@z))+q0;gend=-G@d-Q@(F*(n[:27]@z))+q
    cm=mu+RT*np.log(n/V1[:,None]);Dt=dt*RT*np.sum(mol*(np.log(a)-np.log(bgross)));Dr=-dt*np.sum(V1[:27,None]*rates*(cm[:27]@nu.T))
    Bc=RT*np.sum(n0*np.log(n0/n)-n0+n);We=(d@(K1-K0)@d+d0@(K1-K0)@d0)/4;Wb=(b@(N1-N0)@b+b0@(N1-N0)@b0)/4;Wv=-RT*np.sum(n0*np.log(V1/V0)[:,None]);Ws=dt*lm@s;Dl=dt*loss*(lm@lm);Rn=np.sum(cm*rn)+v@rd
    delta=energy(n,d,b,l,K1,N1,V1)-energy(n0,d0,b0,l0,K0,N0,V0);closure=delta-Ws-We-Wb-Wv+Dt+Dr+Bc+Dl-Rn
    prop=np.max(abs(gend-gstart+G@rd+Q@(F*(rn[:27]@z))));transfer=dt*v@(J@i);portwork=dt*v@p;portclosure=(l@l-l0@l0)/2-portwork-Ws+Dl
    coarse=[];complement=[]
    for indices in boundary:
        x=dt*mol[indices];co=Rface@x;re=x-Sface@co;coarse.append(co.tolist());complement.append(re.tolist())
        assert np.max(abs(Rface@re))<1e-12
    if max(abs(closure),prop,abs(portclosure),abs(q[P.index((1,1,1))]),np.max(abs(Z@(b-b0))))>1e-8 or min(Dt,Dr,Bc,Dl)<-1e-9:raise RuntimeError('ledger unpaid')
    return (n,d,b,q,l),dict(residual=float(err),closure=float(closure),gauss=float(np.max(abs(gend))),propagation=float(prop),portclosure=float(portclosure),minimum=float(np.min(n/V1[:,None])),transfer=float(transfer),portwork=float(portwork),sourcework=float(Ws),loadloss=float(Dl),metricwork=float(We+Wb),volumework=float(Wv),delta=float(delta),edge_forward=(dt*k*a).tolist(),edge_backward=(dt*k*bgross).tolist(),edge_signed=(dt*mol).tolist(),face_coarse=coarse,face_residual=complement,charge_current=i.tolist(),voltage=(J.T@v).tolist(),amount_residual=rn.tolist(),displacement_residual=rd.tolist(),gauss_residual=gend.tolist())

def initial_state(n,model,geom,sign=1.):
    """Synthetic Gauss-compatible initial data with boundary-only q."""
    z,RT,F,*_=model;K,N,V,PP,a=geom
    charge=Q@(F*(n[:27]@z)); q=np.zeros(27)
    boundary_nodes=[k for k,p in enumerate(P) if any(v in (0,2) for v in p)]
    q[boundary_nodes]=charge.sum()/len(boundary_nodes)
    M=np.linalg.inv(K);d=M@(sign*.2*a)
    # Gradient correction to enforce G d = q - Q charge; retain all transverse modes.
    correction=np.linalg.lstsq(G@M@G.T,q-charge-G@d,rcond=None)[0]
    d+=M@G.T@correction
    assert np.max(abs(-G@d-charge+q))<1e-12
    return n.copy(),d,sign*C@a,q,np.zeros(48)

def source_closed_candidate(source_bytes,manifest,pinned_sha256,initial_concentrations,dt):
    """Delegate ORIGINAL admitted closed solver, never reinterpret as open input."""
    from bh4_original_reactive_pnp_adapter import source_bound_closed_implicit_step
    return source_bound_closed_implicit_step(source_bytes,manifest,pinned_sha256=pinned_sha256,initial_concentrations=initial_concentrations,dt=dt)

def assay():
    geom=geometry();K,N,V,PP,a=geom;records=[]
    for ns in (3,29):
        if ns==3:A0=np.array([[1,1,0]]);A1=np.array([[0,0,1]]);z=np.array([1,-1,0]);weights=np.array([[1,0],[0,1],[1,1]])
        else:A0=np.eye(ns)[0:24:2];A1=np.eye(ns)[1:24:2];z=np.repeat(np.arange(15)%3-1,2)[:ns];weights=np.repeat(np.eye(15),2,axis=0)[:ns]
        model=(z,1.,1.,np.zeros(ns),A0,A1,np.full(len(A0),.04),np.full(len(A0),.04))
        c=1+.12*np.sin(np.arange(33*ns).reshape(33,ns));n=c*V[:,None];inv=n.sum(axis=0)@weights
        for sign in (-1,1):
            # Gauss-consistent initial charge: independent boundary displacement.
            state=initial_state(n,model,geom,sign);cond=np.broadcast_to(np.linspace(.04,.08,ns),(108,ns)).copy()
            for t,(s0,s1) in enumerate(((1.,1.),(1.,1.04),(1.04,.97))):
                src=np.zeros(48);src[0]=.3 if t==1 else 0
                state,r=step(*state,.04,model,scaled(geom,s0),scaled(geom,s1),cond,src)
                assert np.max(abs(state[0].sum(axis=0)@weights-inv))<1e-8
                records.append(dict(species=ns,sign=sign,t=t,**r))
    # Lossless frozen material + dynamic exterior trace: conservative reciprocal port.
    z=np.array([1,-1]);empty=np.zeros((0,2));model=(z,1.,1.,np.zeros(2),empty,empty,np.zeros(0),np.zeros(0))
    n=np.ones((33,2))*V[:,None];initial=initial_state(n,model,geom)
    frozen,r=step(*initial,.04,model,geom,geom,np.zeros((108,2)),loss=0)
    assert abs(r['delta'])<1e-10
    mobile,m=step(*initial,.04,model,geom,geom,np.full((108,2),.08),loss=0)
    diff=float(np.linalg.norm(mobile[1]-frozen[1]));assert diff>1e-6
    records.extend([dict(control='frozen',**r),dict(control='mobile',**m)])
    print('steps',len(records),'field difference',diff,'port rank',np.linalg.matrix_rank(PP),'min eig',np.linalg.eigvalsh(K)[0],np.linalg.eigvalsh(N)[0])
    for k in ('residual','closure','gauss','propagation','portclosure','minimum'):
        print(k,min(r[k] for r in records),max(abs(r[k]) for r in records))
    print('controls',[(r['control'],r['delta'],r['portwork'],r['transfer']) for r in records[-2:]])
    print('max boundary residual',max(np.max(abs(np.array(r['face_residual']))) for r in records))
    return records
if __name__=='__main__':assay()
