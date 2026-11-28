"""Original G3 full initial neutral receiver and radial normalization.
P0T/V (#1554), not a finite-time spacetime or physical apparatus.
"""
import sympy as s
import numpy as np
from scipy.integrate import solve_ivp


def eq(a,b=0):
    d=a-b
    assert all(s.simplify(v)==0 for v in (list(d) if isinstance(d,s.MatrixBase) else [d])),d


def exact():
    r,p=s.symbols('r p',positive=True)
    h,b=s.symbols('h b',real=True)
    # Marked frame: n=e3, B in the e1/e3 plane, arbitrary angle.
    u=s.symbols('u',real=True)
    n=s.Matrix([0,0,1]); B=b*s.Matrix([s.sin(u),0,s.cos(u)])
    I=s.eye(3); lap=-b*b/12-h*h
    Hess=h/r*I+(lap-3*h/r)*n*n.T
    F=s.Matrix(3,3,lambda i,j:sum(s.LeviCivita(i,j,k)*B[k] for k in range(3)))
    T=(F*F.T+4*Hess-4*h*h*n*n.T+2*(lap+2*h*h)*I)/(2*p*p)
    a=5*b*b/12+2*h/r+h*h; c=-b*b/6-4*h*h-6*h/r
    eq(p*p*T,a*I+c*n*n.T-B*B.T/2)
    eq(s.trace(T),(7*b*b/12-h*h)/p**2)
    # Recover the magnetic line projector from the marked tidal tensor
    # if radial constraint data are independently known (b != 0).
    eq(2*(a*I+c*n*n.T-p*p*T),B*B.T)
    # Exact two-plane characteristic polynomial, retaining degeneracy.
    z=s.symbols('z'); M=p*p*T-a*I
    eq(M.charpoly(z).as_expr(),z*(z*z-(c-b*b/2)*z-c*b*b*s.sin(u)**2/2))
    x,y,z=s.symbols('x y z',real=True); X=s.Matrix([x,y,z]); D=1+X.dot(X)
    B0=8*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**3
    eq(B0.dot(B0),64/D**4);eq(X.dot(B0),8*z/D**2)
    # Normalization tail bound: V=16 eps²/(3(1+r²)^4), u<=r.
    R,e=s.symbols('R e',positive=True)
    eq(s.integrate(16*e*e*r/(3*(1+r*r)**4),(r,R,s.oo)),8*e*e/(9*(1+R*R)**3))
    print('PASS full tidal matrix, signed-line inverse, spectrum, original source and tail bound')


def numerical(e=.25):
    Q=8*e*e/9; assert Q<1
    def rhs(r,u):return [u[1],-16*e*e*u[0]/(3*(1+r*r)**4)]
    for R in (8.,16.,32.,64.):
        sol=solve_ivp(rhs,(0,R),(0.,1.),rtol=2e-12,atol=2e-14,dense_output=True)
        assert sol.success
        N=sol.y[1,-1]; tail=Q/(1+R*R)**3
        assert 1-Q-1e-10<=N<=1+1e-10 and N>tail
        print('R',R,'finite normalization',N,'analytic omitted derivative bound',tail,'psi0 estimate',1/N)
    # Analytic tail bound excludes ODE integration error: numerical values
    # below are not interval-certified. Compare trace on marked points.
    for X in (np.array([.5,0.,0.]),np.array([.5,.25,.75]),np.array([0.,0.,2.]),np.array([3.,0.,0.])):
        r=np.linalg.norm(X); u,up=sol.sol(r); p=u/(r*N); h=up/u-1/r
        x,y,z=X; D=1+r*r; B=8*e*np.array([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**3
        b2=B@B; n=X/r; a=5*b2/12+2*h/r+h*h; c=-b2/6-4*h*h-6*h/r
        T=(a*np.eye(3)+c*np.outer(n,n)-np.outer(B,B)/2)/p**2
        assert abs(np.trace(T)-(7*b2/12-h*h)/p**2)<1e-12
        assert np.max(abs(2*(a*np.eye(3)+c*np.outer(n,n)-p*p*T)-np.outer(B,B)))<1e-12
        print('point',X.tolist(),'eigenvalues',np.linalg.eigvalsh(T).tolist())
    print('PASS numerical initial receiver diagnostics (not interval or time-evolution certificate)')


if __name__=='__main__':
    exact(); numerical()
