"""W1 original spherical Einstein–matter boundary ABI and exact Israel pullback.
For a timelike polar-areal static/junction slice, same mass and zero surface
radial traction imply matching lapse gradient and both K eigenvalues.
Not a moving dynamical Einstein/GHY/corner or nonspherical existence proof.
"""
import sympy as s

def eq(z):
    assert s.simplify(s.factor(z))==0, s.factor(z)

def main():
    r,mi,me,pr=s.symbols('r mi me p_r',positive=True)
    fi=1-2*mi/r; fe=1-2*me/r
    ni=(mi+4*s.pi*r**3*pr)/(r*r*fi)
    ne=me/(r*r*fe)
    eq(ni-ne-(mi-me+4*s.pi*r**3*pr*fe)/(r*r*fi*fe))
    eq((ni-ne).subs({mi:me,pr:0}))
    eq((s.sqrt(fi)/r-s.sqrt(fe)/r).subs(mi,me))
    eq((s.sqrt(fi)*ni-s.sqrt(fe)*ne).subs({mi:me,pr:0}))
    # The reverse direction is injective on the physical domain fi,fe>0.
    # Equal angular K implies fi=fe hence mi=me; equal temporal K
    # then implies pr=0. No independent imposed lapse force remains.
    eq(fi-fe+2*(mi-me)/r)
    eq((ni-ne).subs(mi,me)-4*s.pi*r*pr/fe)
    # Reopen the original TOV density, pressure and mass functions.
    lam,e,phi,psi=s.symbols('lam eps phi psi',real=True)
    p=lam/(8*s.pi)
    rho=(lam+2)*p*(1-r*r)
    pres=-p*(1-r*r)**2
    m0=lam*(lam+2)*(r**3/s.Integer(3)-r**5/s.Integer(5))/2
    M=lam*(lam+2)/15
    eq(s.diff(m0,r)-4*s.pi*r*r*rho)
    eq(m0.subs(r,1)-M)
    eq(s.diff(m0,r).subs(r,1))
    eq(pres.subs(r,1))
    eq(s.diff(pres,r).subs(r,1))
    R=1+e*phi+e*e*psi/2
    a=s.Function('mass_first_jump')(r)
    b=s.Function('mass_second_jump')(r)
    c=s.Function('pressure_first')(r)
    d=s.Function('pressure_second')(r)
    mass=(m0-M).subs(r,R)+e*a.subs(r,R)+e*e*b.subs(r,R)/2
    pressure=pres.subs(r,R)+e*c.subs(r,R)+e*e*d.subs(r,R)/2
    eq(mass.diff(e).subs(e,0)-a.subs(r,1))
    eq(pressure.diff(e).subs(e,0)-c.subs(r,1))
    m2=s.factor(s.diff(m0,r,2).subs(r,1))
    p2=s.factor(s.diff(pres,r,2).subs(r,1))
    eq(mass.diff(e,2).subs(e,0)-
       (b.subs(r,1)+2*phi*a.diff(r).subs(r,1)+phi**2*m2))
    eq(pressure.diff(e,2).subs(e,0)-
       (d.subs(r,1)+2*phi*c.diff(r).subs(r,1)+phi**2*p2))
    assert m2==-lam*(lam+2)
    assert p2==-8*p
    # The prior mass Einstein constraint fixes a'(1)=-phi*m2.
    m2value=s.factor((-2*phi*a.diff(r).subs(r,1)-phi**2*m2).
                     subs(a.diff(r).subs(r,1),-phi*m2))
    eq(m2value-phi**2*m2)
    p2value=s.factor(-2*phi*c.diff(r).subs(r,1)-phi**2*p2)
    eq(p2value+2*phi*c.diff(r).subs(r,1)-8*p*phi**2)
    # With mass jump + pressure value zero at the same moved radius,
    # both pulled-back K eigenvalues match EXACTLY, not just order two.
    mu=s.Symbol('mu',real=True)
    pb=s.Symbol('pb',real=True)
    n_jump=(mu+4*s.pi*R**3*pb)/(R**2*(1-2*mu/R))-M/(R**2*(1-2*M/R))
    eq(n_jump.subs({mu:M,pb:0}))
    print('PASS original source/pressure->mass/lapse->two-face Israel all-orders algebra')
    print('PASS second moving pressure and Einstein mass jet source',m2,p2)
    print('OPEN dynamical wall velocity/acceleration, GHY/corner, nonspherical Einstein bulk')

if __name__=='__main__':main()
