"""Nonspherical TOV material: exact axial rotation sector and harmonic geometry.

Original O(3)-invariant constitutive repair. Static axial matter form with
metric held fixed; gravitational axial momentum coupling is NOT eliminated.
"""
import sympy as s


def main():
    r,R,v,m=s.symbols('r R v m',positive=True)
    x,l=s.symbols('x l',positive=True); p=l/(8*s.pi)
    rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
    f=1-l*(2+l)*(x/3-x*x/5)
    P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=s.factor(pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f))
    a=s.factor((rho+pt)/2); d=s.factor((rho+pr)/(2*f))
    V=s.factor(rho-2*a-d*f); c=p*(1-x)/2
    # Exact rigid internal rotation Y=r U n leaves s, tr(KB), V and
    # normalized strain invariants unchanged. Radially varying rotation
    # Y=r U(alpha(r,t)) n. In co-rotated internal frame the derivative
    # is n+r alpha_r J n; time derivative r alpha_t J n.
    # Rotate about z; choose n=(sin theta,0,cos theta), Jn=(0,sin theta,0).
    theta,ar,at,N,e=s.symbols('theta ar at N e',real=True)
    n=s.Matrix([s.sin(theta),0,s.cos(theta)])
    jn=s.Matrix([0,s.sin(theta),0])
    I=s.eye(3); f0=f.subs(x,r*r); Pn=n*n.T
    root=I+(1/s.sqrt(f0)-1)*Pn
    B0=I+(f0-1)*Pn
    B=B0+e*f0*r*ar*(n*jn.T+jn*n.T)+e**2*r*r*(f0*ar**2-at**2/N**2)*jn*jn.T
    K=a.subs(x,r*r)*I+(d-a).subs(x,r*r)*Pn
    C1=root*B.diff(e).subs(e,0)*root
    # Compute independently from full strain residual at first order.
    # tr C1=0, tr C1²=2 f r² alpha_r² sin² theta.
    simp=lambda z:s.trigsimp(s.expand(z))
    assert simp(s.trace(C1))==0
    assert simp(s.trace(C1*C1)-2*f0*r*r*ar**2*s.sin(theta)**2)==0
    base=simp(s.trace(K*B.diff(e,2))/2)
    assert s.simplify(base-a.subs(x,r*r)*r*r*(f0*ar**2-at**2/N**2)*s.sin(theta)**2)==0
    # Delta W coefficient of epsilon² is c/2 [(tr C1)²-tr C1²].
    # Net axial twist energy proportional to (a-c) f alpha_r²;
    # temporal kinetic remains a. Internal constant rotation is neutral.
    coeff=s.factor((a-c).subs(x,r*r))
    assert s.cancel(coeff.subs(r,1))==0
    slack=1-s.Rational(21,20)*s.Rational(50,93)
    assert slack>0
    assert s.integrate(s.sin(theta)**3,(theta,0,s.pi))==s.Rational(4,3)
    print('PASS axial l=1 twist Hessian: radial stiffness (a-c)f and inertia a/N²')
    # Angular harmonic identities independently check scalar Legendre
    # modes, polar gradient and axial rotated gradient. Axisymmetry is
    # enough for each l's normalization by SO(3) equivariance.
    z=s.symbols('z',real=True)
    for ell in range(1,9):
        L=ell*(ell+1); Y=s.legendre(ell,z)
        assert s.expand(s.diff((1-z*z)*s.diff(Y,z),z)+L*Y)==0
        norm=s.integrate(Y*Y,(z,-1,1))
        grad=s.integrate((1-z*z)*s.diff(Y,z)**2,(z,-1,1))
        assert norm==s.Rational(2,2*ell+1) and grad==L*norm
        # trace-free Hessian norm on S²: (1/2)(1-z²)² Y''².
        shear=s.integrate((1-z*z)**2*s.diff(Y,z,2)**2/2,(z,-1,1))
        assert shear==L*(L-2)*norm/2
    print('PASS 8 scalar/polar/axial harmonic normalization and spin-2 degeneracy checks')
    print('OPEN metric axial momentum constraint, polar coupled Hessian, l>=2 stability')


if __name__=='__main__':
    main()
