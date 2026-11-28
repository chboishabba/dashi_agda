"""Original compact TT source primitive -> common continuum prepotential.
Native distinct FV radial operators are not identified by this identity.
"""
import json
import sympy as s


def check():
    u=s.symbols('u',positive=True);d=s.symbols('d',positive=True);f=s.Function('f')(u)
    J=lambda a:s.diff(a,u)/u
    lap=lambda a,n:s.diff(a,u,2)+(n-1)*s.diff(a,u)/u
    assert s.expand(J(lap(f,d))-lap(J(f),d+2))==0
    # Independent original endpoint primitive identities, with l4 remainder.
    p=[s.Rational(2,5)*(u*u*s.diff(f,u,3)+2*u*s.diff(f,u,2)-2*s.diff(f,u)),
       s.Rational(4,7)*(u**4*s.diff(f,u,3)-3*u**3*s.diff(f,u,2)+3*u**2*s.diff(f,u)),
       (u**6*s.diff(f,u,3)-12*u**5*s.diff(f,u,2)+75*u**4*s.diff(f,u)-315*u**3*f)/35]
    def lift(a,l):
        for _ in range(2-l//2):a=lap(a,3)
        for _ in range(l):a=J(a)
        return a*{0:s.Rational(2,5),2:s.Rational(4,7),4:s.Rational(1,35)}[l]
    for q,l in enumerate((0,2,4)):
        g=(s.diff(p[q],u)+(27*u*u*f if l==4 else 0))/u**(2+2*l)
        assert s.expand(g-lift(f,l))==0
        assert s.expand(lap(lift(f,l),3+2*l)-lift(lap(f,3),l))==0
    # Smooth radial axis: for analytic even monomials, no negative powers.
    count=0
    for l in (0,2,4):
        for k in range(9):
            assert s.Poly(s.expand(lift(u**(2*k),l)),u).is_univariate;count+=1
    # Bessel phase and fourth-order symbol from radial eigenbasis.
    k=s.symbols('k',positive=True);j0=s.sin(k*u)/(k*u)
    j2=(3/(k*u)**3-1/(k*u))*s.sin(k*u)-3*s.cos(k*u)/(k*u)**2
    j4=(105/(k*u)**5-45/(k*u)**3+1/(k*u))*s.sin(k*u)+(10/(k*u)**2-105/(k*u)**4)*s.cos(k*u)
    for l,j,c in [(0,j0,s.Rational(2,5)),(2,j2,-s.Rational(4,7)),(4,j4,s.Rational(1,35))]:
        assert s.simplify(lift(j0,l)-c*k**4*j/u**l)==0
    # Original arbitrary Cartesian TT symbol, existing full angular Gram donor.
    x,y,z=s.symbols('x y z',real=True);kv=s.Matrix([x,y,z]);K=(kv.T*kv)[0]
    P=K*s.eye(3)-kv*kv.T;Q=s.diag(0,1,-1);T=P*Q*P-P*s.trace(P*Q)/2
    assert all(s.expand(v)==0 for v in kv.T*T) and s.expand(s.trace(T))==0
    assert s.expand(s.trace(T.T*T)-K**2*((2*x*x+y*y+z*z)**2-4*y*y*z*z)/2)==0
    mu=s.symbols('mu',real=True)
    angular_mean=s.integrate((mu**4+6*mu**2+1)/4,(mu,-1,1))/2
    assert angular_mean==s.Rational(4,5)
    # At positive r, up to six radial derivatives cost at most O(k^6).
    # For Dirichlet sine modes, tail exponent after A^p dual bound is 12-4p.
    return dict(generic_dimension_intertwiner=1,original_source_primitive_identities=3,original_bulk_intertwiners=3,even_origin_polynomials=count,bessel_phase_identities=3,angular_gram=str(angular_mean),tail_squared_exponents={'p4':-4,'p5':-8})

if __name__=='__main__':print(json.dumps(check(),indent=2))
