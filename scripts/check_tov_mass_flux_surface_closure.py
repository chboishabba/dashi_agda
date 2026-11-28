"""W2.2: Einstein Misner-Sharp mass/flux integrability and moving vacuum wall.
Exact spherical polar-areal equations; no general material constitutive or
nonlinear Einstein evolution asserted. No-shell vacuum exterior, shared mass.
"""
import sympy as s


def zero(x):
    assert s.simplify(s.factor(x)) == 0, s.factor(x)


def main():
    r,t=s.symbols('r t',positive=True)
    m=s.Function('m')(t,r)
    rho=s.Function('rho')(t,r)
    N=s.Function('N')(t,r)
    f=s.Function('f')(t,r)
    j=s.Function('j')(t,r)
    mr=4*s.pi*r*r*rho
    mt=-4*s.pi*r*r*N*s.sqrt(f)*j
    # Mixed partials of one original Einstein mass function require the
    # exact polar-areal mass/flux integrability source identity.
    continuity=s.factor(s.diff(mr,t)-s.diff(mt,r))
    expected=4*s.pi*(r*r*s.diff(rho,t)+s.diff(r*r*N*s.sqrt(f)*j,r))
    zero(continuity-expected)
    # Independent source with nonzero divergence cannot be sourced by
    # a twice-differentiable common mass on a neighborhood.
    nonconservative=s.simplify(continuity.subs({rho:1,N:1,f:1,j:r}))
    assert nonconservative==12*s.pi*r*r
    # Commuting pullback of an *interior-minus-exterior* mass jump along
    # R(tau). Exterior vacuum Schwarzschild M is constant.
    R,FF,NN=s.symbols('R F N',positive=True);v=s.symbols('v',real=True)
    rh,flux,pressure=s.symbols('rho_wall j_wall p_wall',real=True)
    ut=s.sqrt(FF+v*v)/(NN*s.sqrt(FF))
    mass_rate=s.factor(4*s.pi*R*R*(rh*v-s.sqrt(FF+v*v)*flux))
    flux_required=rh*v/s.sqrt(FF+v*v)
    zero(mass_rate.subs(flux,flux_required))
    # Original W2.1 exact dynamic Israel normal stress on that same face:
    normal=(FF+v*v)*pressure+v*v*rh-2*v*s.sqrt(FF+v*v)*flux
    pressure_required=s.simplify(s.solve(s.Eq(normal.subs(flux,flux_required),0),pressure)[0])
    zero(pressure_required-v*v*rh/(FF+v*v))
    zero(normal.subs({flux:flux_required,pressure:pressure_required},simultaneous=True))
    # Two independent boundary equations are rank two on (j,p), for a
    # fixed rho and wall geometry. rho itself is not supplied by Israel.
    mat=s.Matrix([[-s.sqrt(FF+v*v),0],[-2*v*s.sqrt(FF+v*v),FF+v*v]])
    zero(mat.det()+(FF+v*v)**s.Rational(3,2))
    assert mat.det()!=0
    # Rank-one wall-frame stress: comoving pressureless radial normal
    # tensor; tangential matter stress remains undetermined.
    zero(pressure_required*rh-flux_required**2)
    # For a physical timelike boundary f>0, |j|<rho for rho>0,
    # p<=rho, and zero rho forces zero radial flux and pressure.
    assert s.simplify(1-v*v/(FF+v*v))==FF/(FF+v*v)
    zero(flux_required.subs(rh,0))
    zero(pressure_required.subs(rh,0))
    # Static wall supplies a useful independent no-work limit.
    zero(flux_required.subs(v,0))
    zero(pressure_required.subs(v,0))
    # Non-promotion counterexamples: allowing arbitrary j,p would violate
    # source mass continuity or Israel even with matched boundary f and N.
    assert s.simplify(mass_rate.subs({rh:1,flux:0,v:1}))!=0
    assert s.simplify(normal.subs({pressure:0,rh:0,flux:1,v:1}))!=0
    # The ORIGINAL repaired TOV material source has rho=0 at R=1;
    # algebraic wall compatibility then requires zero wall j,p.
    lam=s.symbols('lam',positive=True)
    rho0=(lam+2)*lam*(1-R*R)/(8*s.pi)
    zero(rho0.subs(R,1))
    zero(flux_required.subs(rh,rho0).subs(R,1))
    zero(pressure_required.subs(rh,rho0).subs(R,1))
    # Moving original material level set: rho_total(R(e),e)=0 to second
    # order, with background radial current identically zero. Thus mass+Israel
    # force actual moving-face j and p to vanish order by order, while the
    # Eulerian second pressure jet need NOT vanish at fixed coordinate r=1.
    e,phi,psi=s.symbols('eps phi psi',real=True)
    x=s.symbols('x',real=True)
    lam0=s.symbols('lambda0',positive=True)
    pscale=lam0/(8*s.pi)
    radpres=-pscale*(1-x*x)**2
    press1=s.Function('p1')(x);press2=s.Function('p2')(x)
    j1=s.Function('j1')(x);j2=s.Function('j2')(x)
    moved=1+e*phi+e*e*psi/2
    pwall=radpres.subs(x,moved)+e*press1.subs(x,moved)+e*e*press2.subs(x,moved)/2
    jwall=e*j1.subs(x,moved)+e*e*j2.subs(x,moved)/2
    zero(pwall.diff(e).subs(e,0)-press1.subs(x,1))
    zero(jwall.diff(e).subs(e,0)-j1.subs(x,1))
    zero(pwall.diff(e,2).subs(e,0)-(press2.subs(x,1)+2*phi*press1.diff(x).subs(x,1)-8*pscale*phi**2))
    zero(jwall.diff(e,2).subs(e,0)-(j2.subs(x,1)+2*phi*j1.diff(x).subs(x,1)))
    print('PASS original second pressure/current wall jets and nonzero Eulerian pressure correction')
    print('PASS Einstein mass integrability, original source counterexample')
    print('PASS moving mass+Israel reverse j,p and rank-two boundary map')
    print('PASS wall stress determinant and TOV zero-density source limit')
    print('OPEN nonlinear matter dynamics, time-dependent exterior, all tensor boundary terms')


if __name__=='__main__':
    main()
