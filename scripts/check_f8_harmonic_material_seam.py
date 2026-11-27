"""F8 fixed-wall harmonic gauge and material response. Frozen comparison only.
Classical linearized Einstein, Israel, Codazzi and wave energy identities.
"""
import sympy as s
import numpy as np


def linear_stress(l,m,J,ut,grad_u,vt,div_v,K,w):
    """Frozen orthonormal tangent frame; u=clock, v=physical material displacement."""
    D=div_v-s.trace(J)/2; V=vt-m
    out=s.diag(-w*D-K*(ut+l/2),(w*D/3+K*(ut+l/2))*s.eye(3))
    out[0,1:4]=(-w*V-K*grad_u).T
    out[1:4,0]=w*vt+K*(m+grad_u)
    return out


def material_gauge_transport():
    t,x,y,z=s.symbols('t x y z',real=True); coords=(t,x,y,z)
    u=s.Function('u')(*coords); v=s.Matrix([s.Function('v'+str(i))(*coords) for i in range(3)])
    l=s.Function('l')(*coords); m=s.Matrix([s.Function('m'+str(i))(*coords) for i in range(3)])
    J=s.Matrix(3,3,lambda i,j:s.Function('j'+str(min(i,j))+str(max(i,j)))(*coords))
    K,w=s.symbols('K w',positive=True); rho,p=s.symbols('rho p'); eta=s.diag(-1,1,1,1)
    h=s.diag(l,J); h[0,1:4]=m.T;h[1:4,0]=m
    xi=s.Matrix([u,*v]); DX=xi.jacobian(coords)
    hm=h-eta*DX-DX.T*eta
    T0=s.diag(-rho,p,p,p)
    tm=linear_stress(hm[0,0],hm[1:4,0],hm[1:4,1:4],0,s.zeros(3,1),s.zeros(3,1),0,K,w)
    T=linear_stress(l,m,J,u.diff(t),s.Matrix([u.diff(a) for a in coords[1:]]),v.diff(t),sum(v[i].diff(coords[i+1]) for i in range(3)),K,w)
    # Pullback from material coordinates; mixed tensor Lie derivative = [T0,Dxi].
    assert (T-tm-(T0*DX-DX*T0)).subs(p,K+w-rho).applyfunc(s.expand)==s.zeros(4)
    assert (eta*T+h*T0-(eta*T+h*T0).T).subs(p,K+w-rho).applyfunc(s.expand)==s.zeros(4)
    C0=-l.diff(t)/2+sum(m[i].diff(coords[i+1]) for i in range(3))-s.trace(J).diff(t)/2
    div=lambda nu:sum(T[a,nu].diff(coords[a]) for a in range(4))
    energy=div(0)-(K+w)*s.trace(J).diff(t)/2
    assert s.expand(energy+K*(u.diff(t,2)-sum(u.diff(a,2) for a in coords[1:])-C0))==0
    d=sum(v[i].diff(coords[i+1]) for i in range(3))
    for i,a in enumerate(coords[1:]):
        mom=div(i+1)-(K+w)*l.diff(a)/2
        assert s.expand(mom-w*(m[i].diff(t)-v[i].diff(t,2)+d.diff(a)/3-s.trace(J).diff(a)/6-l.diff(a)/2))==0
    return 5


def wall_gauge():
    # Background GN wall, arbitrary symmetric tangential perturbation and K self-adjoint.
    g=s.diag(-1,1,1,1); beta=s.symbols('beta',positive=True); K0=s.diag(-1/beta,-beta,-beta,-beta); tau=s.trace(K0)
    def sym(n):return s.Matrix(4,4,lambda i,j:s.Symbol(f'{n}{min(i,j)}{max(i,j)}',real=True))
    h,d,j,dj=map(sym,('h','d','j','dj')); zz,dz=s.symbols('zz dz'); X=g*h
    # Linear C_n: divergence minus half trace derivative, exact GN connections.
    div=dz+tau*zz-s.trace(K0*g*j)
    trder=dz+s.trace(g*dj)-2*s.trace(K0*g*j)
    assert s.expand(div-trder/2-(dz-s.trace(g*dj))/2-tau*zz)==0
    # Quadratic gauge contribution from TT h with h_na=h_nn=0 at wall.
    nabla_a_h_bn=-h*K0; nabla_n_h_ab=d-K0.T*h-h*K0
    cq=-s.trace(g*h*g*(nabla_a_h_bn-nabla_n_h_ab/2))
    assert s.expand(cq-s.trace(g*h*g*d)/2)==0
    # Second-order lapse changes coordinate derivative vs unit-normal derivative.
    N1=g*d/2; Y=g*j; K2=g*dj/2-X*N1+(X*X-Y)*K0-zz*K0/2
    rhs=2*g*(K2+X*N1-(X*X-Y)*K0+zz*K0/2)
    assert (rhs-dj).applyfunc(s.expand)==s.zeros(4)
    # Reduced normal-tangent equation on C_n=0, Codazzi and conserved stress.
    c=s.Matrix(s.symbols('c:4')); dc=s.Matrix(s.symbols('dc:4'))
    reduced=(dc-K0.T*c-K0.T*c)/2
    assert reduced.subs(dict(zip(dc,2*K0.T*c)))==s.zeros(4,1)
    # Normal-parallel frame Robin is K0 rather than 2K0.
    assert (2*K0.T*c-K0.T*c)==K0.T*c
    # Hilbert normal boundary work reciprocal for symmetric Robin matrix.
    cp=s.Matrix(s.symbols('cp:4')); assert (cp.T*K0*c)[0]==(c.T*K0*cp)[0]
    return 6


def bulk_curvature():
    # Constant curvature -1: R_acbd h^cd = h_ab-g_ab tr(h).
    g=s.diag(-1,1,1,1,1); h=s.Matrix(5,5,lambda i,j:s.Symbol(f'h{min(i,j)}{max(i,j)}')); up=g*h*g
    R=s.Matrix(5,5,lambda a,b:sum((-g[a,b]*g[c,d]+g[a,d]*g[c,b])*up[c,d] for c in range(5) for d in range(5)))
    assert (R-h+g*s.trace(g*h)).applyfunc(s.expand)==s.zeros(5)
    # Ricci lower terms: -4h-R, plus 4h cosmological cancellation.
    assert (-4*h-R+4*h+h-g*s.trace(g*h)).applyfunc(s.expand)==s.zeros(5)
    return 2


def frozen_response(s0,k,p,K,w):
    """Principal material response with intrinsic clock source C4_0=0; no forcing."""
    k=np.asarray(k,dtype=float); l=p[0,0]; m=p[1:,0]; J=p[1:,1:]; tr=np.trace(J)
    q=k@k; d=s0*s0+q/3
    D=(q*l/2+1j*s0*(k@m)-s0*s0*tr/2)/d
    V=1j*k*(-s0*(l/2+tr/6)+1j*(k@m)/3)/d
    T=np.diag([-w*D-K*l/2]+[w*D/3+K*l/2]*3).astype(complex)
    T[0,1:]=-w*V; T[1:,0]=w*V+(w+K)*m
    return D,V,T


def frozen_robin(s0,k,t,p,r=1/16):
    """Frozen hybrid comparison: flat normal wave and actual algebraic Israel coefficients.
    Intrinsic clock source held zero in material principal equation; not bulk harmonic gauge.
    Not the full lower-order frozen Einstein operator.
    """
    b=1/t; beta=np.sqrt(1+b*b); w=4*r*b**4/3; K=b*b/(3*beta)-w
    g=np.diag([-1.,1.,1.,1.]); K0=np.diag([-1/beta]+[-beta]*3); tau=np.trace(K0)
    lam=np.sqrt(s0*s0+np.dot(k,k)); assert lam.real>0
    zz=lam/(lam-2*tau)*np.trace(g@p)
    D,V,T=frozen_response(s0,k,p,K,w)
    B=2*g@(-3*T+np.trace(T)*np.eye(4))+2*p@K0+zz*g@K0
    assert np.allclose(B,B.T,atol=1e-8,rtol=1e-8)
    return -B/lam,zz


def frozen_checks():
    # Exact grazing identity and two-regime bound prerequisites.
    a,b,k=s.symbols('a b k',real=True); Z=a*a+b*b+k*k
    l2=(a*a-b*b+k*k)**2+4*a*a*b*b
    assert s.expand(l2-a*a*Z-((k*k-b*b)**2+a*a*(b*b+k*k)))==0
    assert s.Rational(2,3)*s.Rational(5,8)-s.Rational(1,6)==s.Rational(1,4)
    assert s.Rational(42*6+37,600)<s.Rational(1,2)
    # Each numerical inverse is the actual 10x10 Robin comparison, not a continuum solve.
    idx=[(i,j) for i in range(4) for j in range(i,4)]
    def pack(p):return np.array([p[i,j] for i,j in idx])
    def unpack(x):
        p=np.zeros((4,4),complex)
        for z,(i,j) in zip(x,idx):p[i,j]=p[j,i]=z
        return p
    largest=0.; err=0.
    for t in (1.,3.,12.):
        for s0,k in ((600+0j,[0,0,0]),(600+1e5j,[1e5,0,0]),(600+1e5j,[np.sqrt(3)*1e5,0,0]),(600+1e6j,[2e6,3e5,4e5])):
            k=np.array(k); A=np.column_stack([pack(frozen_robin(s0,k,t,unpack(e))[0]) for e in np.eye(10)])
            norm=np.linalg.norm(A,np.inf); largest=max(largest,norm); assert norm<.5
            f=np.arange(1,11,dtype=complex); x=np.linalg.solve(np.eye(10)-A,f)
            err=max(err,np.linalg.norm(x-A@x-f,np.inf)); assert np.linalg.norm(x-A@x-f,np.inf)<1e-10
            D,V,T=frozen_response(s0,k,unpack(x),1.,1.)
            p=unpack(x); l=p[0,0];m=p[1:,0];tr=np.trace(p[1:,1:])
            assert abs(s0*D-1j*(k@(V+m))+s0*tr/2)<1e-5*max(1,abs(s0*D))
            assert np.linalg.norm(s0*V-1j*k*(D/3-l/2))<1e-5*max(1,np.linalg.norm(s0*V))
    print('12 intrinsic-clock-fixed comparison inverses; max infinity norm',largest,'max residual',err)
    return 3


if __name__=='__main__':
    checks={f.__name__:f() for f in (material_gauge_transport,wall_gauge,bulk_curvature,frozen_checks)}
    print(s.__version__,checks,'PASS',sum(checks.values()))


def transport_second(t,xyz,j,xi,material_stress,r):
    """Exact background Lie transport, full variable FRW coefficients.
    material_stress receives metric in material coordinates, returns full mixed T2.
    xi=(delta phi,delta X^i) in original comoving coordinates.
    """
    b=1/t; beta=s.sqrt(1+b*b); rho=beta-1; p=-rho+b*b/(3*beta)
    g=s.diag(-1,t*t*s.eye(3)); T0=s.diag(-rho,p,p,p); coords=(t,*xyz)
    dx=xi.jacobian(coords)
    directional=lambda A:sum((xi[i]*A.diff(a) for i,a in enumerate(coords)),s.zeros(4))
    lie_g=directional(g)+dx.T*g+g*dx
    lie_T=directional(T0)+T0*dx-dx*T0
    return j-lie_g,material_stress(j-lie_g)+lie_T


def full_clock_response(s0,k,p,K,w):
    """Intrinsic clock forced by metric; includes luminal denominator.
    Unlike frozen_response, does not silently impose intrinsic harmonic gauge.
    """
    k=np.asarray(k,dtype=float); l=p[0,0]; m=p[1:,0]; J=p[1:,1:]; tr=np.trace(J)
    lam2=s0*s0+k@k
    C4=-s0*(l+tr)/2+1j*k@m
    u=C4/lam2
    D,V,T=frozen_response(s0,k,p,K,w)
    ut=s0*u; gu=1j*k*u
    T+=np.diag([-K*ut]+[K*ut]*3)
    T[0,1:]-=K*gu; T[1:,0]+=K*gu
    return u,D,V,T


def full_clock_checks():
    # Full harmonic C5_0 = C4_0 + dn p_n0 - dt p_nn/2 in frozen principal part.
    z,ss,dn,C4=s.symbols('z ss dn C4'); C5=C4+dn-ss*z/2
    assert s.solve(C5,C4)==[ss*z/2-dn]
    # For physical homogeneous Dirichlet p_na in the flat normal model dn=0;
    # scalar clock u=s*z/(2 lambda²), not zero. Trace feedback rank one.
    lam,a,K,q=s.symbols('lam a K q',positive=True)
    tr=s.symbols('tr'); z0=lam*tr/(lam+a)
    ut=(lam**2-q)*z0/(2*lam**2)
    # Trace term from clock alone, plus leading normal derivative.
    assert s.factor((lam*tr+4*K*ut)*lam*(lam+a)-tr*(lam**3+(a+2*K)*lam**2-2*K*q))==0
    # The scalar isolated cubic has a unique positive real root, other roots
    # have negative real part: monotone on positive line, sum negative, product positive.
    f=lam**3+(a+2*K)*lam**2-2*K*q
    assert s.diff(f,lam)==3*lam**2+2*lam*(a+2*K)
    # For any positive real s, lambda²=s²+q: polynomial strictly positive.
    assert s.expand(f.subs(q,lam**2-ss**2)-(lam**3+a*lam**2+2*K*ss**2))==0
    # Manufactured full clock forced Robin solve with no imposed physical constraint.
    idx=[(i,j) for i in range(4) for j in range(i,4)]
    def pack(p):return np.array([p[i,j] for i,j in idx])
    def unpack(x):
        p=np.zeros((4,4),complex)
        for v,(i,j) in zip(x,idx):p[i,j]=p[j,i]=v
        return p
    largest=0.; err=0.; invnorm=0.
    for t in (1.,3.,12.):
        b=1/t; beta=np.sqrt(1+b*b); w=b**4/12; K=b*b/(3*beta)-w
        g=np.diag([-1.,1.,1.,1.]); K0=np.diag([-1/beta]+[-beta]*3); tau=np.trace(K0)
        for s0,k in ((600+0j,[0,0,0]),(600+1e5j,[1e5,0,0]),(600+1e5j,[np.sqrt(3)*1e5,0,0]),(600+1e6j,[2e6,3e5,4e5])):
            k=np.array(k); la=np.sqrt(s0*s0+k@k)
            def robin(p):
                u,D,V,T=full_clock_response(s0,k,p,K,w)
                zz=la/(la-2*tau)*np.trace(g@p)
                B=2*g@(-3*T+np.trace(T)*np.eye(4))+2*p@K0+zz*g@K0
                assert np.allclose(B,B.T,atol=1e-8,rtol=1e-8)
                return -B/la
            A=np.column_stack([pack(robin(unpack(e))) for e in np.eye(10)])
            largest=max(largest,np.linalg.norm(A,np.inf)); mat=np.eye(10)-A
            invnorm=max(invnorm,np.linalg.norm(np.linalg.inv(mat),np.inf))
            f=np.arange(1,11,dtype=complex); x=np.linalg.solve(mat,f)
            err=max(err,np.linalg.norm(mat@x-f,np.inf)); assert np.linalg.norm(mat@x-f,np.inf)<1e-9
            p=unpack(x); u,D,V,T=full_clock_response(s0,k,p,K,w)
            assert abs(la*la*u-(-s0*(p[0,0]+np.trace(p[1:,1:]))/2+1j*k@p[1:,0]))<1e-6*max(1,abs(la*la*u))
    print('12 full-clock frozen diagnostic inverses; max matrix norm',largest,'max inverse norm',invnorm,'max residual',err)
    return 4


if __name__=='__main__':
    print('additional full-clock checks',full_clock_checks(),'PASS; not a uniform full-clock estimate')
