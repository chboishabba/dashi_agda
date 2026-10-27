#!/usr/bin/env python3
"""Exact circuit-cutting reconstruction and sampling-variance identities.

This models algebraic *classical reconstruction*, not a SAXON Q hardware run.
Foundational identities: linearity of quantum states/observables and independent
sampling. Original paper attribution remains in
Docs/papers/SaxonQNVMulticore2026SourceAndFormalisationCut.md.
Adaptation/tests: Johl Brown and OpenAI assistant, 2026-10-26.
"""
from fractions import Fraction
from itertools import product

def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), Fraction(0))

def exact_reconstruction(coefficients, component_expectations):
    """Signed/quasiprobability decomposition sum_s a_s E_s."""
    assert len(coefficients) == len(component_expectations)
    return dot(coefficients, component_expectations)

def independent_variance(coefficients, variances):
    """Var(sum_s a_s X_s)=sum_s a_s² Var(X_s) ONLY if X_s independent."""
    assert len(coefficients) == len(variances)
    assert all(v >= 0 for v in variances)
    return sum((a*a*v for a,v in zip(coefficients,variances)), Fraction(0))

def test_exact():
    # A signed expansion with negative weights is still a valid linear identity.
    coeff = [Fraction(3,2), Fraction(-1,2)]
    obs = [Fraction(1,4), Fraction(3,4)]
    assert exact_reconstruction(coeff,obs) == Fraction(0)
    assert independent_variance(coeff,[Fraction(1,9),Fraction(1,4)]) == Fraction(5,16)
    # Multicut expansion factorises for independent *algebraic* components.
    for a,b,c,d in product([Fraction(-1),Fraction(1,2),Fraction(2)],repeat=4):
        left = (a+b)*(c+d)
        expanded = exact_reconstruction([a*c,a*d,b*c,b*d],
                                        [Fraction(1)]*4)
        assert left == expanded
    # A counterexample: covariance changes variance; don't use independence
    # formula for re-used shots or shared estimators.
    a,b = Fraction(1),Fraction(1)
    var1=var2=Fraction(1,4)
    covariance=Fraction(1,4)
    independent=independent_variance([a,b],[var1,var2])
    correlated=independent+2*a*b*covariance
    assert independent == Fraction(1,2)
    assert correlated == Fraction(1)
    print("PASS: exact signed reconstruction, independent variance, covariance counterexample")

if __name__ == "__main__":
    test_exact()
