"""Original G3 Hopf initial receiver: off-axis neutral tides, charged probes,
induced graph cones and complete five-dimensional vacuum trace.
Source #1554 P0T/V/AQ/AP. Classical KK and geodesic deviation.
No finite-time numerical development, actual matter or SI calibration.
"""
import sympy as s


def eq(a,b=0):
    d=a-b
    assert all(s.simplify(v)==0 for v in (list(d) if isinstance(d,s.MatrixBase) else [d])),d


def neutral():
    r,p,e=s.symbols('r p epsilon',positive=True)
    h=s.symbols('h',real=True) # log psi radial derivative
    x,y,z=s.symbols('x y z',real=True)
    n=s.Matrix([x,y,z]); D=1+n.dot(n)
    B=8*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**3
    eq(B.dot(B),64/D**4)
    # Evaluate on marked axis. The exact radial equation fixes Hess log psi.
    B=B.subs({x:0,y:0,z:r})*e
    b2=B.dot(B); lap=-b2/12-h*h
    Hess=s.diag(h/r,h/r,lap-2*h/r)
    grad=s.Matrix([0,0,h]); F=s.Matrix(3,3,lambda i,j:sum(s.LeviCivita(i,j,k)*B[k] for k in range(3)))
    gdd=F*F.T+4*Hess-4*grad*grad.T+2*(lap+2*h*h)*s.eye(3)
    T=gdd/(2*p*p)
    eq(T[0,0],(5*b2/12+2*h/r+h*h)/p**2)
    eq(T[2,2],(-b2/4-4*h/r-3*h*h)/p**2)
    phidd=(-7*b2/12+h*h)/p
    eq(s.trace(T),-phidd/p)
    # radial Newton derivative bound from positive original source:
    # h<0, |h| <= (16/9)eps² r/(1-Q) near centre (using max V).
    # No sign claim for all radii; retain Hessian and signed axis.
    h0=-16*e*e/9
    eq(T.subs(h,h0*r).limit(r,0),s.diag(208,208,-80)*e*e/(9*p*p))
    print('PASS original G3 axial tidal spectrum and radion trace')


def probes():
    # Same KK particle action: L=1/2(g(v,v)+phi²(w+A(v))²).
    # Routh reduction subtracts k*w, not substitutes w in L alone.
    k,w,a,g,phi=s.symbols('k w a g phi',real=True,nonzero=True)
    L=(g+phi**2*(w+a)**2)/2
    wstar=s.solve(s.diff(L,w)-k,w)[0]
    R=s.expand((L-k*w).subs(w,wstar))
    eq(R,g/2+k*a-k*k/(2*phi**2))
    eq(R.subs(k,-k)-R,-2*k*a)
    # Base geodesic force: k F^mu_nu v^nu + k² phi^-3 grad^mu phi.
    # At original time-symmetric centre F0i=0, grad phi=0; no initial
    # spatial force for a rest probe even when k != 0.
    b,vx,vy,vz=s.symbols('b vx vy vz',real=True)
    F=s.Matrix([[0,b,0],[-b,0,0],[0,0,0]])
    v=s.Matrix([vx,vy,vz]); force=k*F*v
    eq(force.dot(v));eq(force.subs({vx:0,vy:0,vz:0}),s.zeros(3,1))
    eq(force.subs(k,-k),-force)
    print('PASS same-action signed compact-momentum Routh and rest control')


def graph():
    # Original G3 centre phi=psi=p, A_z=2eps; initial graph w=0.
    # Compare base and induced metric at the identical marked event.
    p,e=s.symbols('p epsilon',positive=True)
    g=s.diag(-1,p*p,p*p,p*p); A=s.Matrix([0,0,0,2*e])
    H=g+p*p*A*A.T
    eq(H,s.diag(-1,p*p,p*p,p*p*(1+4*e*e)))
    v=s.Matrix([1,0,0,1/(p*s.sqrt(1+4*e*e))])
    eq((v.T*H*v)[0]);eq((v.T*g*v)[0],-4*e*e/(1+4*e*e))
    u=s.Matrix([1,0,0,1/p]);eq((u.T*g*u)[0]);eq((u.T*H*u)[0],4*e*e)
    # Horizontal null lift has compact speed -A(v); it is not graph-bound.
    eq((u.T*g*u)[0]+p*p*(-(A.T*u)[0]+(A.T*u)[0])**2)
    # P0AP graph action derivative on the same initial metric, not an
    # added independent source in the vacuum G3 solution.
    T=s.symbols('tension',positive=True); Delta=1+p*p*(A.T*g.inv()*A)[0]
    eq(Delta,1+4*e*e)
    J=-T*p*p*g.inv()*A/s.sqrt(Delta)
    eq(J[3],-2*T*e/s.sqrt(1+4*e*e))
    eq(J.subs(e,-e),-J)
    print('PASS actual graph versus horizontal causal probe and signed tension current')


if __name__=='__main__':
    neutral();probes();graph()
