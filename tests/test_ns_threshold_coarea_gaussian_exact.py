"""Source-attributed B threshold/coarea and critical-root exact checks.

Rishad Shahmurov, 'Threshold Decomposition of Vorticity Stretching
and Palinstrophy', arXiv:2605.01873v3 (2026-09-10), sections 2-3.
The Gaussian is our calibration, not an original theorem of Shahmurov.
These are NOT proofs of general coarea, R236 identity, or Clay B.
Run: python -m pytest -q tests/test_ns_threshold_coarea_gaussian_exact.py
"""
import sympy as s

def test_radial_gaussian_coarea():
    r,a=s.symbols('r a',positive=True)
    f=s.exp(-r*r)
    # f=a: r=sqrt(-log(a)); |grad f|=2*r*a, area=4*pi*r^2
    surface=8*s.pi*a*(-s.log(a))**s.Rational(3,2)
    # Substitute t=-log(a): a da = -exp(-2t) dt.
    t=s.symbols('t',positive=True)
    layer=8*s.pi*s.integrate(s.exp(-2*t)*t**s.Rational(3,2),(t,0,s.oo))
    bulk=s.integrate(4*s.pi*r*r*(s.diff(f,r))**2,(r,0,s.oo))
    assert s.simplify(layer-bulk)==0
    assert s.simplify(bulk-3*s.pi**s.Rational(3,2)/(2*s.sqrt(2)))==0

def test_critical_vorticity_root_gradient_split():
    f,df,dxi=s.symbols('f df dxi',positive=True)
    # Z=f^(3/4) xi, |xi|=1, xi dot grad xi=0.
    root=s.Rational(3,4)*f**s.Rational(-1,4)
    assert s.simplify(root**2*df**2+f**s.Rational(3,2)*dxi**2-
       (s.Rational(9,16)*f**s.Rational(-1,2)*df**2+
        f**s.Rational(3,2)*dxi**2))==0
