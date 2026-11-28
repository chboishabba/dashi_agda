"""Original compact F8 source: finite Fourier-shell, second-order zero-mode TT replay.
Periodized source, no full R^3 or receiver convergence claim. Uses the existing
variable-time Galerkin owner. No target receiver encoded in the forcing.
"""
import itertools
import argparse
from functools import lru_cache
import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import roots_legendre
from check_f8_tt_retarded import galerkin, geometry, tt_project

EPS=.04
PULSE=.065
Q=np.diag([0.,1.,-1.])
B=np.diag([-2.,1.,1.])

def bump(t):
    d=np.arcsinh(t)-np.sqrt(1+t*t)/t-(np.arcsinh(1.)-np.sqrt(2.))
    if not 0<d<PULSE:return 0.
    return np.exp(1-1/(1-(2*d/PULSE-1)**2))

def radial_coefficient(k,box,quad=128):
    # Fourier series of eps^4 f(|x|/eps), with four derivatives in TT symbol.
    x,w=roots_legendre(quad);u=(x+1)/2
    f=np.exp(1-1/(1-u*u))
    return 4*np.pi*EPS**7*k**4/box**3*np.dot(w/2,u*u*f*np.sinc(k*EPS*u/np.pi))

@lru_cache(maxsize=8)
def quadrature(quad):
    x,w=roots_legendre(quad);return (x+1)/2,w/2

def history(sol,t,n,modes,quad):
    # Reconstruct derivative at FIXED proper normal n from canonical momentum.
    r,w=quadrature(quad)
    L=np.arcsinh(t)-np.arcsinh(.25);Lt=1/np.sqrt(1+t*t)
    freq=np.pi*(np.arange(modes)+.5)
    phi=np.cos(r[:,None]*freq);dp=-np.sin(r[:,None]*freq)*freq
    a,N=geometry(t,L*r); weight=w*L*a**3/N
    M=phi.T@(weight[:,None]*phi); D=phi.T@(weight[:,None]*(-Lt/L*r[:,None]*dp))
    y=sol.sol(t).real; q=y[:modes]; qd=np.linalg.solve(M,y[modes:]-D@q)
    r=np.asarray(n)/L; p=np.cos(r[...,None]*freq); pr=-np.sin(r[...,None]*freq)*freq
    return p@q,p@qd-(Lt/L)*r*(pr@q),(pr@q)/L

def run(box=.4,final=1.2,modes=24,quad=100):
    # Entire first two cubic lattice shells (including both signs), no alias wrap.
    keys=[k for k in itertools.product(range(-1,2),repeat=3) if 0<sum(i*i for i in k)<=2]
    norm={k:sum(i*i for i in k) for k in keys}; shells=sorted(set(norm.values()))
    wave={j:2*np.pi*np.sqrt(j)/box for j in shells}
    coeff={j:radial_coefficient(wave[j],box) for j in shells}
    E={k:tt_project(Q,k) for k in keys}
    pi={k:coeff[norm[k]]*E[k] for k in keys}
    for k in keys:
        assert np.allclose(pi[k],pi[tuple(-i for i in k)])
        assert np.linalg.norm(pi[k]@k)<1e-12 and abs(np.trace(pi[k]))<1e-12
    # H_k(t,n)=h_shell(t,n) Pi_k/spatial amplitude, h_shell already includes coeff.
    sol={j:galerkin(wave[j],lambda t,n:np.zeros_like(n),lambda t,j=j:-6*coeff[j]*bump(t),1.,final,modes,quad)[1] for j in shells}
    # For mean A2 Pi we need controller modes at -k for retained k only.
    # Compute all contributing ordered pairs exactly, no pseudospectral aliasing.
    terms=np.zeros((len(keys),len(shells)))
    for i,k in enumerate(keys):
        for a in keys:
            c=tuple(k[j]-a[j] for j in range(3))
            if c in E:terms[i,shells.index(norm[c])]+=np.sum(pi[a]*E[c])
    assert np.any(terms!=0) # shell sqrt(2) provides genuine triads
    def rhs(t,y):
        h=np.array([sol[j].sol(t)[:modes].real.sum() for j in shells])
        n=len(keys);A,V=y[:n],y[n:]
        return np.r_[V,2*bump(t)*(terms@h)-3*V/t-np.array([wave[norm[k]]**2 for k in keys])*A/t**2]
    ctrl=solve_ivp(rhs,(1.,final),np.zeros(2*len(keys)),rtol=2e-9,atol=1e-14,dense_output=True,method='DOP853')
    assert ctrl.success
    # For an antipodal pair E has transverse eigenvalues +/-p. The spatial
    # STF zero-mode of 2Q_Ricci is 2 p^2(-h_t^2/N^2+h_n^2+2k^2 h^2/a^2) STF(P).
    # Both signs included in the sum below, hence no extra factor two.
    T={j:np.zeros((3,3)) for j in shells}
    for k in keys:
        v=np.asarray(k,float);P=np.eye(3)-np.outer(v,v)/(v@v)
        T[norm[k]]+=np.sum(E[k]*E[k])/2*tt_project(P,[0,0,0])
    def mean_bulk(t,n):
        a,N=geometry(t,n); out=np.zeros(np.shape(n)+(3,3))
        for j in shells:
            h,ht,hn=history(sol[j],t,n,modes,quad)
            val=-ht**2/N**2+hn**2+2*wave[j]**2*h**2/a**2
            out+=val[...,None,None]*T[j]
        return out
    def mean_wall(t):
        # H_0=0; elastic term has zero mean. Controller product is convolution.
        c=ctrl.sol(t)[:len(keys)]
        return -6*bump(t)*tt_project(sum((c[i]*pi[k] for i,k in enumerate(keys)),np.zeros((3,3))),[0,0,0])
    # Bulk quadratic response is even under Q reversal; controller wall
    # term is cubic in Q and odd. Keep BOTH independent diagonal STF rows.
    proj=lambda A,R:np.sum(A*R,axis=(-2,-1))/np.sum(R*R)
    for t in np.linspace(1.,final,7):
        F0=mean_bulk(t,np.linspace(0,.2,5)); G0=mean_wall(t)
        assert np.max(abs(F0-proj(F0,B)[...,None,None]*B))<1e-11*max(1e-15,np.max(abs(F0)))
        assert np.max(abs(G0-proj(G0,Q)*Q))<1e-11*max(1e-25,np.max(abs(G0)))
    fB=lambda t,n:proj(mean_bulk(t,n),B)
    gQ=lambda t:float(proj(mean_wall(t),Q))
    # Scale tiny controller load for numerical accuracy, undo at readout.
    scale=1e12
    JB,_=galerkin(0.,fB,lambda t:0.,1.,final,modes,quad)
    JQ,_=galerkin(0.,lambda t,n:np.zeros_like(n),lambda t:scale*gQ(t),1.,final,modes,quad)
    times=np.linspace(1.,final,401)
    hp=max(abs(sol[j].sol(t)[:modes].sum()) for t in times for j in shells)
    cp=max(np.max(abs(ctrl.sol(t)[:len(keys)])) for t in times)
    gp=max(abs(gQ(t)) for t in times)
    jp=max(abs(JB(t,0.)) for t in times); jq=max(abs(JQ(t,0.))/scale for t in times)
    vals=[hp,cp,gp,jp,jq];assert all(np.isfinite(x) and x>0 for x in vals)
    print('box, final, modes, shells, first modes',box,final,modes,shells,len(keys),flush=True)
    print('radial coeff',coeff,'peaks H_mode A2_mode mean_wall_Q mean_J_B mean_J_Q',vals,'final mean J',JB(final,0.),JQ(final,0.)/scale,flush=True)
    return np.array(vals)


def donor_check():
    # Independently compare against #1530 full Ricci jet on a non-on-shell
    # polarized test. Average four phases, so all quadratic cross terms cancel.
    import sympy as s
    from check_f8_tensor_backreaction import ricci_jet
    T,x,y,v,z=s.symbols('T x y v z',real=True); coords=(T,x,y,v,z)
    f=(1+T*T+T*z+z**3); k=3; h=s.diag(0,0,f*s.cos(k*x),-f*s.cos(k*x),0)/z**2
    dh=[h.diff(q) for q in coords];ddh=[[a.diff(q) for q in coords] for a in dh]
    tt=.7;zz=.8; out=np.zeros((3,3))
    for phase in (0,np.pi/2,np.pi,3*np.pi/2):
        point=dict(zip(coords,(tt,phase/k,0.,0.,zz)))
        ev=lambda A:np.asarray(A.subs(point),float)
        R,_,_=ricci_jet(ev(h),np.array([ev(A) for A in dh]),np.array([[ev(A) for A in row] for row in ddh]),zz)
        out+=2*zz*zz*R[1:4,1:4]/4
    point={T:tt,z:zz};val=lambda A:float(A.subs(point))
    expected=zz**2*(-val(f.diff(T))**2+val(f.diff(z))**2+2*k*k*val(f)**2)*B/6
    assert np.allclose(tt_project(out,[0,0,0]),expected,rtol=1e-12,atol=1e-12)
    print('independent full Ricci jet zero-mode projection PASS',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--final',type=float,default=1.2);p.add_argument('--box',type=float,default=.4);p.add_argument('--modes',type=int,nargs='+',default=[12,24]);a=p.parse_args()
    donor_check()
    for m in a.modes:run(a.box,a.final,m)
