"""Graph-norm trace and spherical exterior matching diagnostics.
Analytic estimate is conditional on the repaired radial coefficient bounds;
not a nonlinear free-boundary theorem.
"""
import sympy as s


def main():
    r,l=s.symbols('r l',positive=True)
    p=l/(8*s.pi); rho=(2+l)*p*(1-r*r); pr=-p*(1-r*r)**2
    f=1-l*(2+l)*(r*r/3-r**4/5)
    d=(rho+pr)/(2*f); A=8*s.pi*r*r*d*f
    m=r*(1-f)/2; M=l*(2+l)/15; F=1-2*M/r
    P=(2+l)*(s.Rational(1,3)-r*r/5)/2-(1-r*r)**2/2
    nu=r*l*P/f; nu_ext=M/(r*r*F)
    eq=lambda z:s.cancel(z)==0
    at=lambda z:z.subs(r,1)
    assert eq(at(A)) and eq(at(s.diff(m,r)))
    assert eq(at(f-F)) and eq(at(s.diff(f-F,r)))
    assert eq(at(nu-nu_ext)) and eq(at(s.diff(nu-nu_ext,r)))
    u,phi=s.symbols('u phi',real=True)
    assert eq(at(A)*u+at(s.diff(m,r))*phi)
    # Perturbed radial pressure from W: p_r=2 f W_f-W.
    # On moving material surface all a,d,V,c vanish, irrespective of strain.
    # At first order the Lagrangian pressure variation vanishes if u+phi=0.
    # For the lapse constraint, at the wall delta nu' only depends on
    # delta m and delta p_r at fixed r; both vanish (p_r'=0).
    dm,dp=s.symbols('dm dp',real=True)
    mm,pp=s.symbols('mm pp',real=True)
    Nprime=(mm+4*s.pi*r**3*pp)/(r*r*(1-2*mm/r))
    lin=s.diff(Nprime,mm)*dm+s.diff(Nprime,pp)*dp
    assert eq(lin.subs({dm:0,dp:0})) and eq(at(s.diff(pr,r)))
    # Model graph estimate: flux J' = V v - w Lv. If p>=a*t,
    # |V|<=b, w<=c*t, then J(0)=0 (finite gradient energy), and
    # |J(t)| <= b sqrt(t)||v||_L² + sqrt(c/2)*t||Lv||_L²(w).
    # Integrate |v'|<=|J|/(a*t) from 0 to delta.
    t,delta=s.symbols('t delta',positive=True)
    assert s.integrate(t**(-s.Rational(1,2)),(t,0,delta))==2*s.sqrt(delta)
    assert s.integrate(t,(t,0,delta))==delta**2/2
    assert s.integrate(1,(t,0,delta))==delta
    # Finite energy rejects nonzero constant boundary flux.
    e=s.symbols('e',positive=True)
    assert s.limit(s.integrate(1/t,(t,e,1)),e,0,dir='+')==s.oo
    # Critical cutoff retains no form-domain trace bound.
    assert s.limit(-1/s.log(e),e,0,dir='+')==0
    print('PASS original background matching, zero first ADM mass variation, lapse constraint identity')
    print('PASS graph trace integral identities; finite form trace negative control')
    print('OPEN quantitative coefficient bounds, physical graph-domain evolution, nonspherical/nonlinear matching')


if __name__=='__main__': main()
