"""A1 exact rational HEAT FLOOR versus false rational HEAT EQUALITY.

Original source: constructive rational density of Murray/Bishop reals,
already in DASHI/Analysis/BishopStrictRatioInterpolationExact.agda;
positive reciprocal comparison in
DASHI/Analysis/BishopPositiveCrossReciprocalUpperExact.agda;
physical viscous rate ν|xi|² in
NSTriadKNEuclideanViscousHeatRateExact.agda.

The old NSClayFacingAPhysicalSameObjectCutExact
PhysicalHighFrequencyEnvelopeData forces embedded rational a to EQUAL
the actual Bishop-real rate. This cannot be populated at generic ν/xi.
The new physicalViscousHeatAdmitsPositiveRationalFloor instead proves
existence of 0<q<actual physical a by constructive rational density.

These checks verify exact irrational/ordered real arithmetic, NOT
Agda kernel typechecking, real inverse monotonicity, nor A2/A3.
"""
import sympy as S

def test_irrational_positive_viscosity_falsifies_rational_equality():
    nu=S.sqrt(2)
    xi=S.Matrix((1,0,0))
    actual=nu*(xi.dot(xi))
    assert actual==S.sqrt(2)
    assert actual.is_rational is False
    # Exact rational witness for this ACTUAL viscosity and frequency:
    q=S.Rational(7,5)
    assert (actual**2-q**2).is_positive
    assert q>0
    assert S.simplify(q<actual) is S.true

def test_positive_rational_lower_floor_bounds_cubic_resolvent_curvature():
    a=S.sqrt(2)
    q=S.Rational(7,5)
    # The actual physical curvature is smaller than the rational-floor
    # upper envelope, unlike a fictitious exact rational identification.
    assert S.simplify(2/a**3 < 2/q**3) is S.true
    assert S.simplify((a/q)**3 < S.Rational(21,20)) is S.true

def test_same_floor_works_for_every_output_of_this_explicit_real_shell():
    nu=S.sqrt(2);q=S.Rational(7,5)
    for xi in ((1,0,0),(0,1,0),(1,1,0),(1,2,3),
               (S.Rational(3,2),0,0)):
        freq=S.Matrix(xi)
        rate=nu*freq.dot(freq)
        assert S.simplify(q<rate) is S.true
        assert S.simplify(2/rate**3 < 2/q**3) is S.true

def test_zero_frequency_must_not_be_given_positive_spectral_floor():
    assert S.sqrt(2)*0==0
    assert not (S.Rational(7,5)<0)
