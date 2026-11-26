"""BJ compactified residual: exact factored connection-difference formula.
JAX finite regression on the closed ball; not a directed interval certificate.
"""
from check_hopf369_p0bh import *
from check_hopf369_p0bj import weight


def ahat(x,eps):
    r=x@x; d=1-r; F=2*(1+r)/h0; a,b,c=x
    W=j.array([2*F**2*a*c-2*F*d*d*b,2*F**2*b*c+2*F*d*d*a,d**4+F**2*(c*c-a*a-b*b)])
    D=d**4+F**2*r
    return eps*h0*(F*d*j.eye(3)+(4*d/h0+4*F)*j.outer(x,x))@W/D**2


def gam3(x):
    I=j.eye(3)
    return h0*(j.einsum('j,ki->kij',x,I)-j.einsum('k,ij->kij',x,I))


def coeffs(x,eps):
    d=1-x@x; a=ahat(x,eps); S=1+d**4*(a@a); al=S**(-.5)
    H=j.eye(3)+d**4*j.outer(a,a); Hi=j.linalg.inv(H)
    D=(h0*d/2)*jax.jacfwd(ahat,0)(x,eps).T-j.einsum('kij,k->ij',gam3(x),a)-2*h0*j.outer(x,a)
    sym=lambda A:(A+A.T)/2
    M=-al*sym(D-d**4*j.outer(a,(D-D.T)@a))
    tf=lambda A:A-j.sum(Hi*A)*H/3
    MT=tf(M)
    def alpha(x):
        d=1-x@x; a=ahat(x,eps)
        return (1+d**4*(a@a))**(-.5)
    da=(h0*d/2)*jax.grad(alpha)(x)
    C0=-J*tf(sym(j.outer(da,a)))-J*al**2*(2-d**4*(a@a))*MT/2
    C1=-3*J*al**2*MT/2
    return a,al,C0,C1


def raw(X,eps,c,t):
    x=X[:3]; y=X[3]; r=x@x; d=1-r; a,al,C0,C1=coeffs(x,eps)
    b=j.cosh(y-L/2)/1.25; I=j.eye(3); g0=j.diag(j.array([b*b,b*b,b*b,1.]))
    aa=j.outer(a,a); root=1/al
    # AN frame difference / delta^2; do not divide by delta.
    P=(b*b-1)*(-d*d*(a@a)/(root*(root+1))*I+al*d*d*aa)+d*d*aa
    A=j.block([[P,a[:,None]],[a[None,:],j.zeros((1,1))]])
    f=y*y*(L-y)**2*(L-2*y)/L**3
    a1,a2,a3=x; H=j.array([1,a1,a2,a3,a1*a2,a1*a3,a2*a3,a1*a1-a2*a2,3*a3*a3-r])
    radial=j.array([(r/(.1+r))**k for k in range(4)])
    Y=j.array([1.]+[fn(k*2*j.pi*y/L) for k in (1,2) for fn in (j.cos,j.sin)])
    p=j.array([y*y*(1-y/L)**3/2,(L-y)**2*(y/L)**3/2])
    lift=1+(b-1)*al
    wh=(j.einsum('i,k,l,ikl->',H,radial,Y,c[:180].reshape(9,4,5))*lift+j.einsum('i,k,l,ikl->',H,radial,p,c[180:].reshape(9,4,2)))/(1+10*r)+t*lift
    u=1/(1+d*d*wh)
    E=-u*(u+1)*wh*g0+u*u*A.at[:3,:3].add(f*(C0-d*d*u*wh*C1))
    return g0,E,lift


def base_gamma(X):
    x=X[:3]; y=X[3]; b=j.cosh(y-L/2)/1.25; bp=j.sinh(y-L/2)/1.25
    G=j.zeros((4,4,4)).at[:3,:3,:3].set(gam3(x))
    G=G.at[3,:3,:3].set(-b*bp*j.eye(3))
    G=G.at[:3,:3,3].set(bp/b*j.eye(3))
    return G.at[:3,3,:3].set(bp/b*j.eye(3))


def scales(X):
    return j.r_[j.repeat(h0*(1-X[:3]@X[:3])/2,3),1.]


def connection(X,eps,c,t):
    g0,E,lift=raw(X,eps,c,t); d=1-X[:3]@X[:3]; g=g0+d*d*E; I=j.linalg.inv(g)
    G=base_gamma(X); ell=j.r_[-h0*X[:3],0.]
    dE=j.moveaxis(jax.jacfwd(lambda X:raw(X,eps,c,t)[1])(X)*scales(X),-1,0)
    U=dE-j.einsum('lij,lk->ijk',G,E)-j.einsum('lik,jl->ijk',G,E)+2*j.einsum('i,jk->ijk',ell,E)
    return .5*j.einsum('ak,ijk->aij',I,U+U.swapaxes(0,1)-U.transpose(1,2,0))


def quotient(X,eps,c,t):
    g0,E,lift=raw(X,eps,c,t); d=1-X[:3]@X[:3]; I=j.linalg.inv(g0+d*d*E)
    G=base_gamma(X); ell=j.r_[-h0*X[:3],0.]; C=connection(X,eps,c,t)
    DC=jax.jacfwd(lambda X:connection(X,eps,c,t))(X)*scales(X)+j.einsum('lkm,mij->lijk',G,C)-j.einsum('mki,lmj->lijk',G,C)-j.einsum('mkj,lim->lijk',G,C)
    R=j.einsum('kijk->ij',DC)-j.einsum('kikj->ij',DC)+2*(j.einsum('k,kij->ij',ell,C)-j.einsum('j,kik->ij',ell,C))+d*d*(j.einsum('kkm,mij->ij',C,C)-j.einsum('kjm,mik->ij',C,C))
    return (3*j.sum(I*E)+j.sum(I*R))/lift


QB=jax.jit(jax.vmap(quotient,(0,None,None,None)))


def run(c):
    eps=.025; X=sample(6,456); Y=X[:16,:3]; Y=Y/np.linalg.norm(Y,axis=1)[:,None]
    T=np.vstack([X,np.c_[Y*.9999,X[:16,3]],np.c_[Y,X[:16,3]]]); Z=j.array(T)
    # Independent original coordinate evaluator, away from delta=0.
    from check_hopf369_p0bj import Wfun
    B,q=evaluate_points(T[:80],eps,c); w=np.asarray(Wfun(j.array(T[:80]),eps))
    for t in (0.,-.04,.04):
        out=np.asarray(QB(Z,eps,c,t)); direct=np.asarray(Rbatch(*B,q+t*w))/w[:,0]
        print('shift',t,'interior max error',np.max(abs(out[:64]-direct[:64])),'near-boundary coordinate difference',np.max(abs(out[64:80]-direct[64:80])),'boundary range',out[80:].min(),out[80:].max(),'boundary approach max',np.max(abs(out[80:]-out[64:80])),flush=True)
        assert np.max(abs(out[:64]-direct[:64]))<1e-8 and np.all(np.isfinite(out))
    zero=np.asarray(QB(Z,0.,np.zeros_like(c),0.));print('zero compactified residual max',np.max(abs(zero)),flush=True);assert np.max(abs(zero))<1e-10
    neg=c.copy();neg[:180].reshape(9,4,5)[:,:,[2,4]]*=-1;neg[180:]=c[180:].reshape(9,4,2)[:,:,::-1].ravel();R=T.copy();R[:,3]=L-R[:,3]
    diff=np.max(abs(np.asarray(QB(Z,eps,c,0.))-np.asarray(QB(j.array(R),-eps,neg,0.))))
    print('signed compactified reflection max',diff,flush=True);assert diff<1e-8
    print('PASS exact normalized formula regression; no interval validation',flush=True)

if __name__=='__main__':
    c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));assert len(c)==252
    run(c)
