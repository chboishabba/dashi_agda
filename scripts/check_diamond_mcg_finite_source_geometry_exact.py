#!/usr/bin/env python3
"""Diamond MCG P2: exact finite-extent axial magnetic-source and array controls.

The axial dipole field kernel has radial dependence 1/r^3, but its
normalisation, orientation and validity are source-specific. Two symmetric
aligned dipoles provide a controlled *test fixture*, NOT a human-heart model.
This deliberately does not reuse the periodic Fourier owner as if it were
the open-space biological Green operator.

Original physics: magnetostatics / magnetic multipole expansion.
Prior repository: DiamondMCGFiniteBridgeExact, existing Maxwell owners,
BalabanConstructiveRationalMatrixInverseExact.
"""
import sympy as sp

def equal(lhs, rhs, msg):
    residual = sp.factor(lhs-rhs)
    assert residual == 0, (msg, residual)

def main():
    r, a = sp.symbols("r a", positive=True)
    # Physical domain: 0 < a < r, observer beyond both source locations.
    near = (r-a)**-3
    far = (r+a)**-3
    finite = sp.Rational(1, 2)*(near+far)
    point = r**-3
    ratio = sp.factor(finite/point)
    error = sp.factor(ratio-1)
    equal(finite, r*(r*r+3*a*a)/(r*r-a*a)**3, "exact finite pair")
    equal(error, a*a*(a**4-3*a*a*r*r+6*r**4)/(r*r-a*a)**3,
          "exact relative dipole error")
    x = sp.symbols("x", positive=True)
    relative = sp.factor(ratio.subs(a,x*r))
    equal(relative, (1+3*x*x)/(1-x*x)**3, "dimensionless finite-size ratio")
    equal(sp.diff(relative,x), 12*x*(1+x*x)/(1-x*x)**4,
          "strict increasing finite-size correction")
    equal(sp.limit(relative,x,0), 1, "dipole far-field limit")
    equal(sp.limit((relative-1)/x**2,x,0), 6, "leading quadrupolar correction")
    # Exact certified bound for a/r <= 1/2 via monotonic correction:
    # 0 <= relative error <= relative(1/2)-1 = 61/27? compute exactly.
    upper=sp.factor(relative.subs(x,sp.Rational(1,2))-1)
    print("Exact relative error bound for a/r<=1/2:",upper)
    # Spatial array gradient: two point sensors separated 2h at r-h, r+h.
    h=sp.symbols("h",positive=True)
    response_left=(r-h)**-3
    response_right=(r+h)**-3
    gradient=sp.factor(response_left-response_right)
    equal(gradient,2*h*(3*r*r+h*h)/(r*r-h*h)**3,
          "two-sensor dipole gradient")
    equal(sp.limit(gradient/h,h,0),6/r**4,
          "gradient far-field r^-4 limit")
    # Projected cardiac power for two differently located sensors.
    projected=sp.Matrix([response_left,response_right])
    projector=sp.eye(2)-sp.ones(2,2)/2
    equal(sp.factor((projector*projected).dot(projector*projected)),
          sp.factor(gradient**2/2),"common-mode suppression signal loss")
    # Equal-sensor point-field spatial mode is exactly erased.
    assert projector*sp.ones(2,1)==sp.zeros(2,1)
    # Finite pair response after symmetrical source averaging:
    finite_left=sp.factor(finite.subs(r,r-h))
    finite_right=sp.factor(finite.subs(r,r+h))
    # Numeric exact rational inputs are a mathematical fixture, not measured.
    for radius,halfwidth,baseline in [
        (sp.Rational(1),sp.Rational(1,20),sp.Rational(1,50)),
        (sp.Rational(10),sp.Rational(1,20),sp.Rational(1,2)),
        (sp.Rational(1000),sp.Rational(1,20),sp.Rational(5))]:
        assert radius > halfwidth+baseline
        vals=[sp.factor(v.subs({r:radius,a:halfwidth,h:baseline}))
              for v in (finite_left,finite_right)]
        assert vals[0]>vals[1]>0
        finite_info=sum(v*v for v in vals)
        projected_info=sp.factor((vals[0]-vals[1])**2/2)
        assert 0<projected_info<finite_info
        print("PASS finite array fixture r=",radius,"relative spatial retention=",
              float(projected_info/finite_info))
    print("PASS exact finite-source, dipole expansion and spatial target-loss identities")
    print("OPEN: tissue-return-current model, sensor transfer, measured covariance, attribution.")

if __name__=="__main__":main()
