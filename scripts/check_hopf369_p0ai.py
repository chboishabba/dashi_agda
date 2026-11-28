"""Original G3/X6 initial graph, inverse Israel stress; no bulk evolution.
Generic KK spatial Christoffel identity, axis evaluation and source controls.
"""
import sympy as s
import numpy as np
from scipy.integrate import solve_ivp


def exact():
    a=s.Matrix(s.symbols('a:3',real=True)); l=s.Matrix(s.symbols('l:3',real=True))
    D=s.Matrix(3,3,s.symbols('d:9',real=True)) # D_ij=partial_i a_j
    S=1+a.dot(a); H=s.eye(3)+a*a.T; Hi=s.eye(3)-a*a.T/S
    # g0=(I+aa^T,a;a^T,1); inverse vertical row=(-a^T,S).
    g=H.row_join(a).col_join(a.T.row_join(s.ones(1,1)))
    derivatives=[g.diff(a[0])*D[i,0]+g.diff(a[1])*D[i,1]+g.diff(a[2])*D[i,2] for i in range(3)]+[s.zeros(4)]
    row=list(-a)+[S]; F=D-D.T
    Gamma=s.Matrix(3,3,lambda i,j:s.expand(sum(row[k]*(derivatives[i][k,j]+derivatives[j][k,i]-derivatives[k][i,j])/2 for k in range(4))))
    P=(D+D.T)/2-((F*a)*a.T+a*(F*a).T)/2+H*a.dot(l)
    assert (Gamma-P+H*a.dot(l)).applyfunc(s.expand)==s.zeros(3)
    # X6 shape acceleration is trace of induced spatial connection.
    expected=s.trace(D)+3*a.dot(l)-a.dot(D*a)/S
    assert s.cancel(s.trace(Hi*P)-expected)==0
    ep,z,p,lp=s.symbols('eps z psi lp',real=True); w=1+z*z; az=2*ep/w; d=4*ep*z/w**2; sz=1+az**2
    pz=P.subs(dict(zip(list(a)+list(l)+list(D),[0,0,az,0,0,lp,d,-4*ep/w**2,0,4*ep/w**2,d,0,0,0,-d])))
    assert (pz-s.diag(d+az*lp,d+az*lp,-d+sz*az*lp)).applyfunc(s.simplify)==s.zeros(3)
    # Vacuum Gauss, trace-free probe, reflection and held-one-side obstruction.
    k,T=s.symbols('k T',positive=True); q=s.symbols('q:3',real=True)
    K=s.diag(-sum(q),*q); I=s.eye(4); stress=-T*I; J=-k*(stress-s.trace(stress)*I/3)
    Q=lambda X:s.trace(X)**2-s.trace(X*X)
    assert s.trace(K)==0 and s.expand(Q(K)+sum(q)**2+sum(x*x for x in q))==0
    assert s.expand(Q(K+J)-Q(K))==4*k*k*T*T/3
    assert s.trace(K+J/2)==-2*k*T/3
    assert s.expand(s.trace(-2*K/k))==0
    print('PASS generic 9 spatial connection components, X6 trace, axial form, vacuum Gauss and one-sided tension incompatibility')


def axis(eps=.25):
    sol=solve_ivp(lambda r,u:[u[1],-eps**2*64/(12*(1+r*r)**4)*u[0]],(0,64),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
    normal=sol.y[1,-1]
    def probe(z):
        r=abs(z); u,up=sol.sol(r); p=(u/r if r else 1)/normal
        lp=(up/u-1/r)*np.sign(z) if r else 0.; a=2*eps/(1+z*z); d=4*eps*z/(1+z*z)**2; S=1+a*a
        # mixed spatial principal K; same common normal as W2 graph w=0
        kx=-(d+a*lp)/(p*np.sqrt(S)); kz=-(-d+S*a*lp)/(p*S**1.5)
        K=np.array([-2*kx-kz,kx,kx,kz]); rho=2*K[0] # kappa=1, reflected S=-2K, rho=-S^0_0
        return K,rho,-K@K
    for z in (0.,.5,1.,2.,4.,8.,16.):
        K,rho,R=probe(z); Km,rhom,Rm=probe(-z)
        assert np.max(abs(K+Km))<1e-13 and abs(rho+rhom)<1e-13 and abs(R-Rm)<1e-13
        if z: assert rho>0 and rhom<0 and R<0
        else: assert not np.any(K)
        print('axis z',z,'K mixed',K.tolist(),'rho reflected',rho,'R_h',R)

if __name__=='__main__': exact();axis()
