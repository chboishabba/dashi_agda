"""Exact unforced NS directional-curvature negative control for the
Permana--Lathief--Ibrahim 2026 manuscript, preserving author attribution.

Source claim (Zenodo 19632058 v3 abstract):
    ||grad(xi)|| <= C_nu |omega|^(1/2)
on high-vorticity regions. A universal viscosity-only constant C_nu,
without further frequency, initial-H^s, T3 or geometric hypotheses,
CANNOT follow from NS alone. The counterexample uses smooth actual
unforced heat solutions, with arbitrarily high |grad xi| at fixed
strictly positive |omega| at positive time. This does NOT refute
conditional estimates with source-written additional hypotheses,
or the classical Constantin--Fefferman direction regularity theorem.
"""
import sympy as S

x,t,A=S.symbols("x t A",real=True,positive=True)

def fields(n):
    u=S.Matrix([0,A*S.exp(-t)*S.sin(x),
                A*S.exp(-n*n*t)*S.sin(n*x)])
    omega=S.Matrix([0,-S.diff(u[2],x),S.diff(u[1],x)])
    return u,omega

def test_exact_unforced_heat_shear_NS():
    for n in (2,3,5,9):
        u,om=fields(n)
        assert S.simplify(S.diff(u,t)-S.diff(u,x,2))==S.zeros(3,1)
        # u is independent of y,z while u_x=0, so (u.grad)u=0.
        assert u[0]==0
        assert S.simplify(om[1]+A*n*S.exp(-n*n*t)*S.cos(n*x))==0

def test_vorticity_direction_gradient_at_high_intensity():
    for n in (2,3,5,10,40):
        _,om=fields(n)
        x0=S.pi/(2*n)
        magnitude=S.simplify(om[2].subs(x,x0))
        assert S.simplify(magnitude-A*S.exp(-t)*S.cos(x0))==0
        derivative=S.diff(om[1],x).subs(x,x0)
        grad_direction=S.simplify(S.Abs(derivative)/magnitude)
        assert S.simplify(
            grad_direction-n*n*S.exp(-(n*n-1)*t)/S.cos(x0))==0
        # t_n>0: ||grad xi||/sqrt(|omega|) grows proportional to n²
        tt=S.Rational(1,n*n)
        ratio=S.simplify(
            (grad_direction/S.sqrt(magnitude)).subs({A:4,t:tt}))
        assert S.N(ratio)>n*n/6

def test_no_universal_viscosity_only_curvature_constant():
    ratios=[]
    for n in (5,10,20,40):
        _,omega=fields(n)
        x0=S.pi/(2*n);tt=S.Rational(1,n*n)
        magnitude=omega[2].subs({x:x0,t:tt,A:4})
        grad=S.Rational(n*n)*S.exp(-(n*n-1)*tt)/S.cos(x0)
        ratios.append(float(S.N(grad/S.sqrt(magnitude))))
        assert float(S.N(magnitude))>3.0
    assert ratios==sorted(ratios)
    assert ratios[-1]/ratios[0]>30

def test_constant_high_vorticity_magnitude_everywhere_destroys_uniform_curvature_rate():
    # Stronger than the localized-point example: the WHOLE TORUS
    # is a high-vorticity region for any fixed threshold < A/e.
    x,t,nu,A=S.symbols("x t nu A",positive=True,real=True)
    for n in (2,3,5,12,40):
        factor=A*S.exp(-nu*n*n*t)
        u=S.Matrix((0,factor*S.sin(n*x)/n,
                       factor*S.cos(n*x)/n))
        omega=S.Matrix((0,-S.diff(u[2],x),S.diff(u[1],x)))
        direction=S.Matrix((0,S.sin(n*x),S.cos(n*x)))
        assert S.simplify(S.diff(u,t)-nu*S.diff(u,x,2))==S.zeros(3,1)
        assert S.simplify(omega-factor*direction)==S.zeros(3,1)
        assert S.simplify((omega.T*omega)[0]-factor**2)==0
        assert S.simplify(
            (S.diff(direction,x).T*S.diff(direction,x))[0]-n*n)==0
        # t_n=1/(nu*n²)>0; vorticity magnitude A/e and |grad xi|=n
        # at EVERY spatial point.
        tN=1/(nu*n*n)
        assert S.simplify(factor.subs(t,tN)-A*S.exp(-1))==0
    n=S.symbols("n",positive=True)
    assert S.limit(n/S.sqrt(A/S.E),n,S.oo)==S.oo
