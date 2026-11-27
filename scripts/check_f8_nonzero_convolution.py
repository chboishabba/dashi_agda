"""Continuous nonzero-output F8 TT convolution, finite radial band diagnostics.
No spatial periodization. Original source and fixed action, not receiver convergence.
"""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.interpolate import CubicSpline
from scipy.special import roots_legendre
from check_f8_original_zero_history import radial_coefficient, bump
from check_f8_homogeneous_mass import lifted_history
from check_f8_tt_retarded import galerkin, geometry

Q=np.diag([0.,1.,-1.])
I=np.eye(3)

def project(A,k):
    P=I-np.outer(k,k)/(k@k) if k@k else I
    A=(A+A.T)/2
    return P@A@P-P*np.trace(P@A)/(2 if k@k else 3)


def connection(E,k):
    # Fourier derivative i*k; return real C/i.
    return (np.einsum('i,lj->lij',k,E)+np.einsum('j,li->lij',k,E)-np.einsum('l,ij->lij',k,E))/2


def intrinsic(E,G,p,q):
    # Ordered quadratic spatial Ricci after dropping a pure longitudinal gradient.
    return np.einsum('kl,k,lij->ij',E,q,connection(G,q))+np.einsum('kjl,lik->ij',connection(E,p),connection(G,q))


def exact():
    # Direct Christoffel expansion for two nonparallel, TT polynomial histories
    # in the physical Poincare metric. Spatial projection kills trace/gradient.
    T,z,x,y,v=s.symbols('T z x y v',real=True); X=(T,z,x,y,v); eps=s.symbols('eps')
    p=s.Matrix([1,0,0]);q=s.Matrix([0,2,0]);E=s.diag(0,1,-1);G=s.Matrix([[0,0,1],[0,0,0],[1,0,0]])
    h=E*(1+T*z)*s.exp(s.I*x)+G*(T*T+z**3)*s.exp(2*s.I*y)
    g=s.diag(-1,1,1,1,1)/z**2; H=s.diag(s.zeros(2),h)/z**2; gi=g.inv(); ix=range(5)
    from itertools import product
    def conn(dg,inv):
        return {(a,b,c):sum(inv[a,l]*(dg[l,c].diff(X[b])+dg[l,b].diff(X[c])-dg[b,c].diff(X[l]))/2 for l in ix) for a,b,c in product(ix,repeat=3)}
    C0=conn(g,gi); C1a=conn(H,gi); C1b=conn(g,-gi*H*gi); C1={i:s.expand(C1a[i]+C1b[i]) for i in C0}
    C2a=conn(H,-gi*H*gi); C2b=conn(g,gi*H*gi*H*gi); C2={i:s.expand(C2a[i]+C2b[i]) for i in C0}
    def ric(i,j):
        return s.expand(sum(C2[k,i,j].diff(X[k])-C2[k,i,k].diff(X[j]) for k in ix)+sum(C0[k,k,l]*C2[l,i,j]+C1[k,k,l]*C1[l,i,j]+C2[k,k,l]*C0[l,i,j]-C0[k,j,l]*C2[l,i,k]-C1[k,j,l]*C1[l,i,k]-C2[k,j,l]*C0[l,i,k] for k,l in product(ix,repeat=2)))
    r=p+q; P=s.eye(3)-r*r.T/(r.T*r)[0]; proj=lambda A:(P*A*P-P*s.trace(P*A)/2).applyfunc(s.expand)
    # Extract cross mode e^{i(x+2y)} using polynomial variables.
    a,b=s.symbols('a b'); cross=lambda f:s.expand(f.subs({s.exp(s.I*x):a,s.exp(2*s.I*y):b})).coeff(a,1).coeff(b,1)
    # expand complex exponent products automatically via explicit exp rewrite.
    cross=lambda f:s.expand(f).subs({s.exp(s.I*x):a,s.exp(2*s.I*y):b}).expand().coeff(a,1).coeff(b,1)
    actual=s.Matrix(3,3,lambda i,j:2*z*z*cross(ric(i+2,j+2)))
    f=1+T*z; j=T*T+z**3
    def C(A,k,l,i,j):return (k[i]*A[l,j]+k[j]*A[l,i]-k[l]*A[i,j])/2
    def B(A,B,p,q):return s.Matrix(3,3,lambda i,j:sum(A[k,l]*q[k]*C(B,q,l,i,j)+C(A,p,k,j,l)*C(B,q,l,i,k) for k,l in product(range(3),repeat=2)))
    want=z*z*((-f.diff(T)*j.diff(T)+f.diff(z)*j.diff(z))*(E*G+G*E)+2*f*j*(B(E,G,p,q)+B(G,E,q,p)))
    assert proj(actual-want)==s.zeros(3)
    assert proj(want)!=s.zeros(3)
    # Exact polynomial azimuth rule: direction components degree 1, TT projectors
    # degree <=4, connection degree <=5, intrinsic product degree <=10.
    for m in range(1,11):assert abs(np.exp(2j*np.pi*m*np.arange(16)/16).sum())<1e-12
    print('independent nonparallel full Ricci cross-mode parity and azimuth controls PASS',flush=True)


def tri(k,p,q):
    """Triangle aligned along e3. Exact azimuth trapezoid for degree <=10."""
    c=(k*k+p*p-q*q)/(2*k*p); rho=p*np.sqrt(max(0.,1-c*c)); z=p*c
    a=2*np.pi*np.arange(16)/16
    P=np.column_stack((rho*np.cos(a),rho*np.sin(a),np.full(16,z)))
    return P,np.array([0.,0.,k])-P


def radial_tri(k,cutoff,r,rw,a,w):
    for p,wp in zip(r,rw):
        lo=abs(k-p);hi=min(k+p,cutoff)
        if hi<=lo:continue
        for q,wq in zip(lo+(hi-lo)*(a+1)/2,(hi-lo)*w/2):
            yield p,q,wp*wq*p*q/(4*np.pi**2*k)


def run(cutoff=80.,nodes=6,histories=8,modes=12,final=1.12,quad=80,kout=30.):
    # Output direction is physical y, choose right-handed frame (z,x,y).
    # Both output polarizations are retained by reflection symmetry; cross is zero.
    rot=I[:,[2,0,1]]; Q0=rot.T@Q@rot; axis=np.array([0.,0.,kout]); R=np.diag([1.,-1.,0.])
    proj=lambda A:np.sum(project(A,axis)*R)/2
    a,w=roots_legendre(nodes);r=cutoff*(a+1)/2;rw=cutoff*w/2
    kh=cutoff*(1-np.cos(np.linspace(0,np.pi,histories)))/2
    sol=[lifted_history(k,1.,final,modes,quad) for k in kh]
    cc=lambda k:radial_coefficient(k,1.)
    # Scalar controller angular response diagonalizes by SO(2) type around its
    # output direction. Use unit-norm STF representatives of m=0,1,2.
    reps=[np.diag([-1.,-1.,2.])/np.sqrt(6),np.array([[0.,0.,1.],[0.,0.,0.],[1.,0.,0.]])/np.sqrt(2),np.diag([1.,-1.,0.])/np.sqrt(2)]
    kr=np.r_[0.,kh[1:]]; tables=[]
    for k in kr[1:]:
        qs=[];weights=[]
        for p,q,wt in radial_tri(k,cutoff,r,rw,a,w):
            pp,qq=tri(k,p,q);z=[np.mean([np.sum(project(S,P)*project(S,Qv)) for P,Qv in zip(pp,qq)]) for S in reps]
            qs.append(q);weights.append(wt*cc(p)*cc(q)*np.array(z))
        tables.append((np.array(qs),np.array(weights)))
    # k=0 response per unit STF norm: angular mean tr E²=2/5.
    scale=1e8; nK=len(kr)
    def rhs(t,y):
        hv=np.array([f(t,0.)[0] for f in sol]);interp=CubicSpline(kh,hv)
        Z=np.zeros((nK,3));Z[0,:]=np.dot(rw*r*r*np.array([cc(k)**2 for k in r]),interp(r))/(5*np.pi**2)
        for i,(qs,W) in enumerate(tables,1):Z[i]=W.T@interp(qs)
        B=y[:3*nK].reshape(nK,3);V=y[3*nK:].reshape(nK,3)
        return np.r_[V.ravel(),(2*scale*bump(t)*Z-3*V/t-kr[:,None]**2*B/t**2).ravel()]
    ctrl=solve_ivp(rhs,(1.,final),np.zeros(6*nK),rtol=2e-8,atol=1e-11,dense_output=True,method='DOP853');assert ctrl.success
    # Precompute actual nonzero output pair kernels and controller wall weights.
    ps=[];qs=[];B=[];C=[];W=[]
    for p,q,wt in radial_tri(kout,cutoff,r,rw,a,w):
        pp,qq=tri(kout,p,q); b0=[];c0=[];w0=[]
        for P,Qv in zip(pp,qq):
            E=project(Q0,P);G=project(Q0,Qv);d=Qv/q;dQ=Q0@d;z=d@dQ
            m0=1.5*z*z;m1=2*(dQ@dQ-z*z);m2=np.sum(Q0*Q0)-m0-m1
            b0.append(proj(E@G));c0.append(proj(intrinsic(E,G,P,Qv)));w0.append(proj(E)*np.array([m0,m1,m2]))
        ps.append(p);qs.append(q);B.append(wt*cc(p)*cc(q)*np.mean(b0));C.append(wt*cc(p)*cc(q)*np.mean(c0));W.append(wt*cc(p)*np.mean(w0,axis=0))
    ps,qs,B,C,W=map(np.array,(ps,qs,B,C,W)); koutsol=lifted_history(kout,cc(kout),final,modes,quad)
    def F(t,n):
        vals=np.array([f(t,n) for f in sol]);interp=CubicSpline(kh,vals,axis=0);hp,htp,hnp=np.moveaxis(interp(ps),1,0);hq,htq,hnq=np.moveaxis(interp(qs),1,0)
        a0,N=geometry(t,n)
        return B@(-htp*htq/N**2+hnp*hnq)+2*(C@(hp*hq))/a0**2
    def gctrl(t):
        b=ctrl.sol(t)[:3*nK].reshape(nK,3)/scale
        return -6*bump(t)*np.sum(W*CubicSpline(kr,b,axis=0)(qs))
    # Separate each contribution for signed diagnostics. Elastic result is per mu*S.
    gela=lambda t:6*proj(Q0)*koutsol(t,0.)[0]
    zf=lambda t,n:np.zeros_like(n); zg=lambda t:0.
    Jb,_=galerkin(kout,F,zg,1.,final,modes,quad)
    Jc,_=galerkin(kout,zf,lambda t:1e9*gctrl(t),1.,final,modes,quad)
    Je,_=galerkin(kout,zf,gela,1.,final,modes,quad)
    result=np.array([Jb(final,0.).real,Jc(final,0.).real/1e9,Je(final,0.).real]);assert np.all(np.isfinite(result)) and np.all(result!=0)
    print('nonzero output k',kout,'cutoff/nodes/histories/modes',cutoff,nodes,histories,modes,'bulk,controller,elastic per mu*S',result.tolist(),flush=True)
    return result

if __name__=='__main__':
    exact()
    for n,h in ((4,6),(6,8)):run(nodes=n,histories=h)
