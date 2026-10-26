"""NS A1 Bishop-real heat-rate / rational reciprocal semantic acceptance.

Original analytical source: Murray/Bishop rational density and positive
reciprocal antitonicity, as already represented in the existing
BishopStrictRatioInterpolationExact and
BishopPositiveCrossReciprocalUpperExact Agda owners.

This locally checks exact irrational/shell semantics of the
source-written positiveRationalFloorBoundsPhysicalInverse theorem.
It is NOT an Agda kernel certificate, a physical resolvent/Gram
identification, an A2 domination theorem or unrestricted Clay A.
"""
import sympy as s

def test_strict_real_reciprocal_floor():
    a=s.sqrt(2); q=s.Rational(7,5)
    assert s.simplify(q<a) is s.true
    assert s.simplify(1/a<1/q) is s.true
    assert s.simplify(1/a**3<1/q**3) is s.true

def test_uniform_shell_reciprocal_on_real_frequencies():
    nu=s.sqrt(2);floor=s.Rational(7,5)
    for xi in [(1,0,0),(0,1,0),(1,1,0),(2,1,3),
               (s.Rational(3,2),0,0)]:
        rate=s.simplify(nu*sum(z*z for z in xi))
        assert s.simplify(floor<rate) is s.true
        assert s.simplify(1/rate<=1/floor) is s.true
        assert s.simplify(1/rate**3<=1/floor**3) is s.true

def test_no_global_positive_floor_on_punctured_continuum():
    nu=s.sqrt(2)
    for q in [s.Rational(1,100),s.Rational(1,2),s.Rational(7,5)]:
        xi=q/(4*nu)
        rate=s.simplify(nu*xi**2)
        assert s.simplify(rate<q) is s.true

def test_correct_scalar_inverse_does_not_pay_physical_gram():
    a=s.sqrt(2);q=s.Rational(7,5)
    source=s.symbols('M',positive=True)
    assert s.simplify(1/a<=1/q) is s.true
    assert s.limit(source/a,source,s.oo)==s.oo
