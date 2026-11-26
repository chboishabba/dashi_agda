"""BL: first-order weak-form kernel certificate for the original projected trial.
Exact integration-by-parts reduction; sampled matrices are NOT interval bounds.
"""
from check_hopf369_p0bk_projection import *
from check_hopf369_p0bj_compact import coeffs,base_gamma,scales


def what(X,al,c):
    x,y=X[:3],X[3]; a,b,d=x; r=x@x
    H=j.array([1,a,b,d,a*b,a*d,b*d,a*a-b*b,3*d*d-r])
    radial=j.array([(r/(.1+r))**k for k in range(4)])
    Y=j.array([1.]+[fn(k*2*j.pi*y/L) for k in (1,2) for fn in (j.cos,j.sin)])
    P=j.array([y*y*(1-y/L)**3/2,(L-y)**2*(y/L)**3/2])
    f0=1+(j.cosh(y-L/2)/1.25-1)*al
    return (f0*j.einsum('i,k,l,ikl->',H,radial,Y,c[:180].reshape(9,4,5))+j.einsum('i,k,l,ikl->',H,radial,P,c[180:].reshape(9,4,2)))/(1+10*r)


def fields(X,eps,c,cs):
    x,y=X[:3],X[3]; r=x@x; d=1-r; a,al,C0,C1=coeffs(x,eps)
    b=j.cosh(y-L/2)/1.25; I=j.eye(3); g0=j.diag(j.array([b*b,b*b,b*b,1.]))
    aa=j.outer(a,a); root=1/al
    P=(b*b-1)*(-d*d*(a@a)/(root*(root+1))*I+al*d*d*aa)+d*d*aa
    A=j.block([[P,a[:,None]],[a[None,:],j.zeros((1,1))]])
    f=y*y*(L-y)**2*(L-2*y)/L**3
    # m=2 projection. All operations regular at delta=0.
    wh=(1-r*r)*((1-r*r)*what(X,al,c)+r*r*what(X,al,cs));u=1/(1+d*d*wh)
    E=-u*(u+1)*wh*g0+u*u*A.at[:3,:3].add(f*(C0-d*d*u*wh*C1))
    Dhat=j.zeros((4,4)).at[:3,:3].set(u**3*f*C1)
    return g0,E,Dhat,u,al


def energy(X,eps,c,cs):
    x,y=X[:3],X[3]; d=1-x@x
    g0,E,Dh,u,al=fields(X,eps,c,cs);g=g0+d*d*E;D=d*d*Dh;I=j.linalg.inv(g)
    G0=base_gamma(X);ell=j.r_[-h0*x,0.];sc=scales(X)
    def derivatives(X):
        _,E,Dh,_,_=fields(X,eps,c,cs);return j.stack([E,Dh])
    de,dd=j.moveaxis(jax.jacfwd(derivatives)(X)*sc,-1,1)
    def cov0(T,dT):
        return d*d*(dT-j.einsum('lij,lk->ijk',G0,T)-j.einsum('lik,jl->ijk',G0,T)+2*j.einsum('i,jk->ijk',ell,T))
    dg=cov0(E,de);dD0=cov0(Dh,dd)
    C=.5*j.einsum('ak,ijk->aij',I,dg+dg.swapaxes(0,1)-dg.transpose(1,2,0))
    dD=dD0-j.einsum('lij,lk->ijk',C,D)-j.einsum('lik,jl->ijk',C,D)
    Dr=I@D@I;tr=j.sum(I*D);dDr=j.einsum('ia,kab,bj->kij',I,dD,I)
    W=2*I+Dr;T=j.einsum('ij,kij->k',W,C)-j.einsum('ik,lil->k',W,C)
    # Physical boundary coefficient 6j+[nu.T], realized as [nu.Z]*6.
    _,_,_,us,als=fields(X.at[3].set(0.),eps,c,cs)
    m=-1+(als+1/als)/us
    B=j.tanh(y-L/2);s=j.sqrt(I[3,3]);Z=j.array([0.,0.,0.,B*s*m])
    # Ordinary y derivative in this x-dependent frame; the base is parallel.
    dy_g=dg[3]+j.einsum('lj,lk->jk',G0[:,3,:],g)+j.einsum('lk,jl->jk',G0[:,3,:],g)
    sy=-(I@dy_g@I)[3,3]/(2*s)
    divZ=m*((1-B*B)*s+B*sy)+.5*j.sum(I*dy_g)*Z[3]
    M=(6+tr)*I-Dr
    V1=I@j.einsum('ij,kij->k',I,dD)-j.einsum('iik->k',dDr)
    lin=V1+2*T-12*Z
    V=3*j.sum(W*g0)+j.einsum('kij,kij',dDr,C)-j.einsum('jij,kik',dDr,C)+j.einsum('ij,kkl,lij',W,C,C)-j.einsum('ij,kjl,lik',W,C,C)-6*divZ
    return M,lin,V,V-.25*lin@j.linalg.solve(M,lin),g,C,Dr,m,V1,T,Z


EB=jax.jit(jax.vmap(energy,(0,None,None,None)))


def verify_identity(c):
    cs=projected_coefficients(c);eps=.025
    from check_hopf369_p0bj import weight
    def eta(X):return weight(X,eps)*(1+.1*X[0]*j.cos(2*j.pi*X[3]/L))
    def v(X):return fields(X,eps,c,cs)[3]*eta(X)
    def flux(X):
        M,l,V,S,g,C,D,m,V1,T,Z=energy(X,eps,c,cs)
        value=v(X);p=jax.grad(v)(X)*scales(X)
        return -value*M@p-value**2*(V1+T-6*Z)
    def one(X):
        M,l,V,S,g,C,D,m,V1,T,Z=energy(X,eps,c,cs)
        value=v(X);p=jax.grad(v)(X)*scales(X)
        F=flux(X);dF=jax.jacfwd(flux)(X)*scales(X)
        div=j.trace(dF)+j.einsum('iik,k->',base_gamma(X)+C,F)
        q=qjet(X,eps,c);qs=qjet(X,eps,cs)
        # Separate coordinate evaluator: obtain original BG and projected jets then use existing taper product rule analytically.
        def w(X):
            r=X[:3]@X[:3];return (1-r*r)*((1-r*r)*(bg.enriched(X,eps,4,2)@c)+r*r*(bg.enriched(X,eps,4,2)@cs))
        ww=j.concatenate([j.atleast_1d(w(X)),jax.grad(w)(X),jax.hessian(w)(X).ravel()]);ee=j.concatenate([j.atleast_1d(eta(X)),jax.grad(eta)(X),jax.hessian(eta)(X).ravel()])
        strong=-value*jax.grad(res,3)(*block_jets(X,eps),ww)@ee
        weak=p@M@p+value*l@p+V*value**2
        return strong,weak+div
    X=sample(4,135);X[:,:3]*=.8
    a,b=np.asarray(jax.jit(jax.vmap(one))(j.array(X)))
    print('independent strong/weak divergence identity max',np.max(abs(a-b)),flush=True);assert np.max(abs(a-b))<1e-8


def exact():
    b,B,s0=s.symbols('b B S',positive=True);u,j0=s.symbols('u j',real=True,nonzero=True)
    # Boundary contraction of the actual Christoffel jump and background jump.
    assert s.simplify(-12*j0-(-6*j0*(1+s0*s0)/(u*s0))-6*j0*(-2+(s0+1/s0)/u))==0
    # Reference normal shift B=b'/b; div Z=1+2 B².
    M=s.diag(6/b**2,6/b**2,6/b**2,6);ell=s.Matrix([0,0,0,-12*B]);V=24-6*(1+2*B**2)
    assert s.simplify(V-(ell.T*M.inv()*ell)[0]/4-18*(1-B**2))==0
    print('PASS physical Robin flux reduction and reference energy Schur margin',flush=True)


def run(c):
    cs=projected_coefficients(c);eps=.025
    X=sample(10,456);z=sample(7,814);n=z[:,:3]/np.linalg.norm(z[:,:3],axis=1)[:,None]
    T=np.vstack([X,*[np.c_[n*r,z[:,3]] for r in (.9,.99,.999,.9999,1.)]])
    x=sample(6,987)[:,:3];Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    T=np.vstack([T,Z]);rows=[]
    for k in range(0,len(T),128):
        M,l,V,S,g,C,D,m,*_=map(np.asarray,EB(j.array(T[k:k+128]),eps,c,cs))
        rows.append(np.c_[np.linalg.eigvalsh(M).min(axis=1),S,V,np.max(abs(C),axis=(1,2,3)),np.max(abs(D),axis=(1,2)),m])
    a=np.vstack(rows)
    for name,v in [('bulk',a[:1024]),('tail incl boundary',a[1024:1664]),('seam',a[1664:])]:
        print(name,len(v),'principal min',v[:,0].min(),'Schur min/max',v[:,1].min(),v[:,1].max(),'V min',v[:,2].min(),'C max',v[:,3].max(),'D raised max',v[:,4].max(),'m min/max',v[:,5].min(),v[:,5].max(),flush=True)
    assert np.min(a[:,:2])>0
    # zero and signed reflection: principal eigenvalues and Schur scalar invariant.
    Z=T[:128];M,l,V,S,*_=map(np.asarray,EB(j.array(Z),0.,np.zeros_like(c),np.zeros_like(c)))
    target=18*h0*h0/(np.cosh(Z[:,3]-L/2)/1.25)**2
    print('zero Schur discrepancy',np.max(abs(S-target)),flush=True);assert np.max(abs(S-target))<1e-10
    neg=c.copy();neg[:180].reshape(9,4,5)[:,:,[2,4]]*=-1;neg[180:]=c[180:].reshape(9,4,2)[:,:,::-1].ravel();R=Z.copy();R[:,3]=L-R[:,3]
    M,l,V,S,*_=map(np.asarray,EB(j.array(R),-eps,neg,projected_coefficients(neg)))
    print('signed Schur discrepancy',np.max(abs(S-a[:128,1])),flush=True);assert np.max(abs(S-a[:128,1]))<1e-8
    # Verify physical seam jump of T against algebra, using actual one-sided C.
    Z=T[-128:];M,l,V,S,g,C,D,m,*_=map(np.asarray,EB(j.array(Z),eps,c,cs));I=np.linalg.inv(g);W=2*I+D
    Tvec=np.einsum('nij,nkij->nk',W,C)-np.einsum('nik,nlil->nk',W,C)
    flux=Tvec[:,3]/np.sqrt(I[:,3,3]);jump=flux[:64]-flux[64:]
    print('boundary flux identity max',np.max(abs(jump-6*J*(m[:64]-1))),flush=True);assert np.max(abs(jump-6*J*(m[:64]-1)))<1e-8

if __name__=='__main__':
    exact();c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));assert len(c)==252;run(c);verify_identity(c)
