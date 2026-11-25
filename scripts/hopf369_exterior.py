"""Conforming cubical Maxwell collar, same P0Y material work.
Frozen original KK graph metric; finite reflecting outer boundary (natural H trace).
Synthetic kinetics; not a radiation condition, physical brane or bulk solution.
"""
import numpy as np
from itertools import product, combinations
from scipy.integrate import solve_ivp, quad
from scipy.linalg import cho_factor, cho_solve
from scipy.optimize import root
from numpy.polynomial.legendre import leggauss
import hopf369_dual_midpoint as z

def shift(p,i):
    q=list(p);q[i]+=1;return tuple(q)
def move(p):return tuple(x-1 for x in p)
P=list(product(range(-2,3),repeat=3)); cells=list(product(range(-2,2),repeat=3))
E=[(i,p) for i in range(3) for p in P if p[i]<2]
F=[(i,j,p) for i,j in combinations(range(3),2) for p in P if p[i]<2 and p[j]<2]
pi={p:i for i,p in enumerate(P)};ei={p:i for i,p in enumerate(E)};fi={p:i for i,p in enumerate(F)}
G=np.zeros((len(P),len(E)),int);C=np.zeros((len(F),len(E)),int);Z=np.zeros((len(cells),len(F)),int)
for l,(i,p) in enumerate(E):G[pi[p],l]=-1;G[pi[shift(p,i)],l]=1
for l,(i,j,p) in enumerate(F):
    for k,q,sgn in ((i,p,1),(j,shift(p,i),1),(i,shift(p,j),-1),(j,p,-1)):C[l,ei[k,q]]=sgn
for l,p in enumerate(cells):
    for k in range(3):
        i,j=[a for a in range(3) if a!=k];sgn=(-1)**k
        Z[l,fi[i,j,p]]=-sgn;Z[l,fi[i,j,shift(p,k)]]=sgn
assert (len(P),len(E),len(F),len(cells))==(125,300,240,64)
assert not np.any(C@G.T) and not np.any(Z@C)
ip=np.array([pi[move(p)] for p in z.P]);ie=np.array([ei[i,move(p)] for i,p in z.edges]);iff=np.array([fi[i,j,move(p)] for i,j,p in z.faces])
assert np.array_equal(G[np.ix_(ip,ie)],z.G) and np.array_equal(C[np.ix_(iff,ie)],z.C)
J=np.zeros((300,108));J[ie]=z.J
Q=np.zeros((125,27));Q[ip]=z.Q
B=np.zeros((125,108));B[ip]=z.E
assert np.array_equal(G@J-B,Q@z.V)

def assemble(order=4,eps=.25):
    sol=solve_ivp(lambda r,u:[u[1],-eps**2*64/(12*(1+r*r)**4)*u[0]],(0,64),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
    norm=sol.y[1,-1]
    def metric(x):
        r=np.linalg.norm(x);psi=(sol.sol(r)[0]/r if r else 1)/norm;a=eps*z.A(x)
        return psi**2*(np.eye(3)+np.outer(a,a))
    t,w=leggauss(order);t=(t+1)/2;w=w/2
    local=[]; supports=[]; facecounts=np.zeros((2,240),int)
    for region in (0,1):
        M=np.zeros((300,300));N=np.zeros((240,240));ee=set();ff=set()
        for ci,p in enumerate(cells):
            if int(not all(a in (-1,0) for a in p))!=region:continue
            ed=[];eb=[];fd=[];fb=[]
            for i in range(3):
                tr=[k for k in range(3) if k!=i]
                for bits in product((0,1),repeat=2):
                    q=list(p)
                    for k,v in zip(tr,bits):q[k]+=v
                    ed.append(ei[i,tuple(q)]);eb.append((i,tr,bits))
            for i,j in combinations(range(3),2):
                k=3-i-j
                for v in (0,1):
                    q=list(p);q[k]+=v;fd.append(fi[i,j,tuple(q)]);fb.append((k,v))
            ee.update(ed);ff.update(fd);facecounts[region,fd]+=1
            me=np.zeros((12,12));nf=np.zeros((6,6))
            for ijk in product(range(order),repeat=3):
                x=t[list(ijk)];g=metric(np.array(p)+x);v=np.sqrt(np.linalg.det(g));wt=np.prod(w[list(ijk)])
                a=np.zeros((3,12));b=np.zeros((3,6))
                for k,(i,tr,bits) in enumerate(eb):a[i,k]=np.prod([x[j] if l else 1-x[j] for j,l in zip(tr,bits)])
                for l,(k,vv) in enumerate(fb):b[k,l]=(-1)**k*(x[k] if vv else 1-x[k])
                me+=wt*a.T@(v*np.linalg.inv(g))@a;nf+=wt*b.T@(g/v)@b
            M[np.ix_(ed,ed)]+=me;N[np.ix_(fd,fd)]+=nf
        local.append((M,N));supports.append((ee,ff))
    se=sorted(supports[0][0]&supports[1][0]);sf=sorted(supports[0][1]&supports[1][1]);assert len(se)==48 and len(sf)==24
    # Integer oriented boundary of both cell sets, including outer shell boundary.
    interior=np.array([all(a in (-1,0) for a in p) for p in cells]);bi=Z[interior].sum(axis=0);bo=Z[~interior].sum(axis=0)
    assert np.all(bi[sf]==-bo[sf]) and np.count_nonzero(bi)==24 and np.count_nonzero(bi+bo)==96
    assert np.array_equal(np.flatnonzero((facecounts[0]>0)&(facecounts[1]>0)),sf)
    Mi,Ni=local[0];Mo,No=local[1];M=Mi+Mo;N=Ni+No
    assert min(np.linalg.eigvalsh(M))>0 and min(np.linalg.eigvalsh(N))>0
    # P0Z metric/volumes and oriented edge assembly checked in same order.
    K0,N0,vol,_,_=z.geometry(eps,order)
    assert np.max(abs(Mi[np.ix_(ie,ie)]-np.linalg.inv(K0)))<1e-12
    assert np.max(abs(Ni[np.ix_(iff,iff)]-N0))<1e-12
    seed=np.array([eps*quad(lambda u:z.A(np.array(p)+np.eye(3)[i]*u)[i],0,1,epsabs=1e-12)[0] for i,p in E])
    return M,N,Mi,Ni,Mo,No,vol,np.array(se),np.array(sf),seed

def setup_step(geom,dt):
    M,N,Mi,Ni,Mo,No,vol,se,sf,seed=geom
    cf=cho_factor(2*M+dt**2/2*C.T@N@C)
    X=cho_solve(cf,dt*J)
    return cf,X

def step(state,geom,dt,model,k,cache):
    n0,e0,b0,q0=state;M,N,Mi,Ni,Mo,No,vol,se,sf,_=geom
    val,RT,Fc,mu,A0,A1,kf,kb=model;nu=A1-A0
    assert np.all(nu@val==0) and np.max(abs(RT*np.log(kf/kb)+nu@mu),initial=0)<1e-10
    cf,X=cache;vfree=cho_solve(cf,2*M@e0+dt*C.T@N@b0)
    def terms(n,v):
        c=n/vol[:,None];xi=(J.T@v)[:,None]*Fc*val/RT
        a=c[z.left]*z.bern(-xi);b=c[z.right]*z.bern(xi);mol=k*(a-b);cur=Fc*(mol@val)
        rates=np.exp(np.log(c[:27])@A0.T)*kf-np.exp(np.log(c[:27])@A1.T)*kb
        f=z.Vhat@mol;f[:27]+=vol[:27,None]*(rates@nu)
        return f,cur,a,b,mol,rates
    size=n0.size
    def unpack(x):return np.exp(np.clip(x[:size].reshape(n0.shape),-60,60)),x[size:]
    def residual(x):
        n,v=unpack(x);f,cur,*_=terms(n,v)
        return np.r_[(n-n0-dt*f).ravel(),v-vfree+X@cur]
    if np.any(k) or len(kf):
        sol=root(residual,np.r_[np.log(n0).ravel(),vfree],options={'xtol':1e-10});assert np.all(np.isfinite(sol.x)) and np.max(abs(sol.x[:size]))<59
        n,v=unpack(sol.x)
    else:n,v=n0.copy(),vfree
    f,cur,a,b,mol,rates=terms(n,v);e=2*v-e0;bn=b0-dt*C@v;bm=(bn+b0)/2;q=q0+dt*B@cur
    rn=n-n0-dt*f;rd=M@(e-e0)-dt*(C.T@N@bm-J@cur)
    err=max(np.max(abs(rn)),np.max(abs(rd)));assert err<1e-9
    # Opposite interface reaction from the TWO local cell assemblies.
    pin=C.T@Ni@bm-J@cur-Mi@(e-e0)/dt
    pout=C.T@No@bm-Mo@(e-e0)/dt
    mask=np.ones(300,bool);mask[se]=False
    assert max(np.max(abs(pin[mask])),np.max(abs(pout[mask])),np.max(abs(pin+pout)))<1e-8
    Ui=lambda e,b:.5*(e@Mi@e+b@Ni@b)
    Uo=lambda e,b:.5*(e@Mo@e+b@No@b)
    port=dt*v@pin;outer=dt*v@pout;transfer=dt*v@J@cur
    ic=Ui(e,bn)-Ui(e0,b0)+port+transfer;oc=Uo(e,bn)-Uo(e0,b0)+outer
    mu1=mu+RT*np.log(n/vol[:,None]);chem=lambda n:np.sum(n*(mu+RT*(np.log(n/vol[:,None])-1)))
    Dt=dt*RT*np.sum(mol*(np.log(a)-np.log(b)));Dr=-dt*np.sum(vol[:27,None]*rates*(mu1[:27]@nu.T));Bc=RT*np.sum(n0*np.log(n0/n)-n0+n)
    Rnum=np.sum(mu1*rn)+v@rd
    delta=Ui(e,bn)+Uo(e,bn)+chem(n)-Ui(e0,b0)-Uo(e0,b0)-chem(n0)
    closure=delta+Dt+Dr+Bc-Rnum
    g0=-G@M@e0-Q@(Fc*(n0[:27]@val))-q0;g=-G@M@e-Q@(Fc*(n[:27]@val))-q
    prop=np.max(abs(g-g0+G@rd+Q@(Fc*(rn[:27]@val))))
    assert max(abs(closure),abs(ic),abs(oc),prop,np.max(abs(g)),np.max(abs(Z@(bn-b0))))<1e-8
    assert min(Dt,Dr,Bc)>-1e-9 and abs(q.sum()-Fc*np.sum(n[27:]@val))<1e-8
    assert np.max(abs(q[np.setdiff1d(np.arange(125),ip)]))<1e-12 and abs(q[pi[(0,0,0)]])<1e-12
    # Actual complete cochain and boundary complements, no reduction to port power.
    boundary_payload=[dt*mol[ix] for ix in z.boundary];coarse=[z.Rface@a for a in boundary_payload];complement=[a-z.Sface@c for a,c in zip(boundary_payload,coarse)]
    return (n,e,bn,q),dict(residual=err,closure=closure,inner=ic,outer=oc,port=port,outer_port=outer,gauss=np.max(abs(g)),propagation=prop,transfer=transfer,minimum=np.min(n/vol[:,None]),delta=delta,interface_e=v[se].copy(),interface_b=bn[sf].copy(),interface_reaction=pin[se].copy(),opposite_reaction=pout[se].copy(),edge_forward=dt*k*a,edge_backward=dt*k*b,edge_signed=dt*mol,face_coarse=coarse,face_residual=complement,charge_residual=g,amount_residual=rn,displacement_residual=rd)

def assay():
    geom=assemble();M,N,Mi,Ni,Mo,No,vol,se,sf,seed=geom;dt=.12;cache=setup_step(geom,dt)
    # Divergence-free exterior magnetic pulse on same original Hopf background.
    ext=np.zeros(300);ext[ei[1,(2,-1,0)]]=.5
    val=np.array([1,-1,0]);A0=np.array([[1,1,0]]);A1=np.array([[0,0,1]])
    model=(val,1.,1.,np.zeros(3),A0,A1,np.array([.04]),np.array([.04]));n=np.ones((33,3))*vol[:,None]
    init=(n,np.zeros(300),C@(seed+ext),np.zeros(125));weights=np.array([[1,0],[0,1],[1,1]])
    records=[];final=[]
    # Exact coordinate BIDI and Schur complement of the actual exterior field.
    outside=np.setdiff1d(np.arange(300),ie);Am=2*M+dt**2/2*C.T@N@C
    Aoo=Am[np.ix_(outside,outside)];Aio=Am[np.ix_(ie,outside)];Aii=Am[np.ix_(ie,ie)]
    schur=Aii-Aio@np.linalg.solve(Aoo,Aio.T);assert min(np.linalg.eigvalsh(schur))>0
    rhs=dt*C.T@N@init[2];vi=np.linalg.solve(schur,rhs[ie]-Aio@np.linalg.solve(Aoo,rhs[outside]));vo=np.linalg.solve(Aoo,rhs[outside]-Aio.T@vi)
    reconstructed=np.zeros(300);reconstructed[ie]=vi;reconstructed[outside]=vo
    schur_error=np.max(abs(reconstructed-np.linalg.solve(Am,rhs)));assert schur_error<1e-12
    print('Schur reconstruction error',schur_error,'Schur eigenvalue',min(np.linalg.eigvalsh(schur)))
    assert np.array_equal((C@ext)[iff],np.zeros(36))
    # Compare a second trajectory with the same original interior and no exterior pulse.
    state=(n.copy(),np.zeros(300),C@seed,np.zeros(125));kzero=np.zeros((108,3))
    for k in range(24):state,r=step(state,geom,dt,model,kzero,cache)
    control=state

    for mobility in (0.,.08):
        # Keep reactions in both cases; initial equilibrium so frozen field control is conservative.
        state=tuple(a.copy() for a in init);rr=[]
        for k in range(24):
            state,r=step(state,geom,dt,model,np.full((108,3),mobility),cache);rr.append(r)
            assert np.max(abs((state[0]-n).sum(axis=0)@weights))<1e-8
        records+=rr;final.append(state)
        ports=np.array([r['port'] for r in rr]);print('mobility',mobility,'port min/max/sum',ports.min(),ports.max(),ports.sum(),'ionic work',sum(r['transfer'] for r in rr),'total delta',sum(r['delta'] for r in rr))
        assert ports.min()<0 and ports.max()>0
    pulse_diff=np.linalg.norm(final[0][1][ie]-control[1][ie]);assert pulse_diff>1e-6
    print('exterior-only pulse final interior difference',pulse_diff)
    # Full 29/12 synthetic dimensional test, neutral paired charges.
    ns=29;val=np.repeat(np.arange(15)%3-1,2)[:ns];val[-1]=-val[:-1].sum();A0=np.eye(ns)[0:24:2];A1=np.eye(ns)[1:24:2]
    model=(val,1.,1.,np.zeros(ns),A0,A1,np.full(12,.04),np.full(12,.04));n29=np.ones((33,ns))*vol[:,None]
    s29,r=step((n29,np.zeros(300),C@(seed+ext),np.zeros(125)),geom,dt,model,np.full((108,ns),.04),cache);records.append(r)
    assert np.max(abs((s29[0]-n29).sum(axis=0)@np.repeat(np.eye(15),2,axis=0)[:ns]))<1e-8
    print('steps',len(records),'interface',len(se),len(sf),'field difference',np.linalg.norm(final[1][1]-final[0][1]),'min eig',np.linalg.eigvalsh(M)[0],np.linalg.eigvalsh(N)[0])
    for k in ('residual','closure','inner','outer','gauss','propagation','minimum'):print(k,min(r[k] for r in records),max(abs(r[k]) for r in records))
    print('max residual boundary',max(np.max(np.abs(r['face_residual'])) for r in records))
    return records
if __name__=='__main__':assay()
