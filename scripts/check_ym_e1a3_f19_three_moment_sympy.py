#!/usr/bin/env python3
"""SymPy exact original E1 cutoff3/F19 weighted 3-moment diagnostic.
Uses the actual source-shaped conditional 512-case Q8 Wilson slice
from check_ym_native_f19_weighted_slice_sympy.py. At beta(1)=0 the
independent original bare coarse one-link Q8 marginal is uniform.
This does NOT prove physical SU(N) full Haar RG contraction or E1
changing-cutoff continuum estimates. No CI/Agda.
"""
from pathlib import Path
from runpy import run_path
import sympy as sp

source = run_path(str(Path(__file__).with_name(
    "check_ym_native_f19_weighted_slice_sympy.py")))
Q8 = source["Q8"]
weights = source["weights"]
z = source["z"]
Z = source["Z"]
assert len(Q8) == 8 and all(weights[w].subs(z, 1) == 64 for w in Q8)
assert Z.subs(z, 1) == 512

def coarse_f(w):
    return sp.Integer(2 * w[0] if w[1] == 0 else 0)

def coarse_g(w):
    return sp.Integer(1 if w == (1, 0) else -1 if w == (-1, 0) else 0)

def eff(h):
    return sp.factor(sum(weights[w] * h(w) for w in Q8) / Z)

def bare(h):
    return sp.Rational(1, 8) * sum(h(w) for w in Q8)

def fg(w):
    return coarse_f(w) * coarse_g(w)

# F19 grouped expectation and original E1 cutoff3 blocked expectation
# share the SAME slice partition and moments (checked in upstream file).
# Compare to the INDEPENDENT beta(1)=0 bare coarse Q8 expectation.
for h in (coarse_f, coarse_g, fg):
    assert sp.simplify(eff(h).subs(z, 1) - bare(h)) == 0

dF = sp.factor(eff(coarse_f) - bare(coarse_f))
dG = sp.factor(eff(coarse_g) - bare(coarse_g))
dFG = sp.factor(eff(fg) - bare(fg))
CovE = sp.factor(eff(fg) - eff(coarse_f) * eff(coarse_g))
CovB = sp.factor(bare(fg) - bare(coarse_f) * bare(coarse_g))
# This is EXACT original E1/R445 3-moment telescope.
assert sp.factor(CovE-CovB-dFG+dF*eff(coarse_g)
                 +bare(coarse_f)*dG) == 0

for coupling in (sp.Rational(1, 2), sp.Integer(1),
                 sp.Integer(2), sp.Integer(3)):
    evaluate = lambda x: sp.factor(x.subs(z, coupling))
    eF = evaluate(dF)
    eG = evaluate(dG)
    eFG = evaluate(dFG)
    covariance_error = evaluate(CovE - CovB)
    telescope = sp.factor(eFG - eF * evaluate(eff(coarse_g))
                          - bare(coarse_f) * eG)
    bound = (abs(eFG) + abs(eF) * abs(evaluate(eff(coarse_g)))
             + abs(bare(coarse_f)) * abs(eG))
    assert covariance_error == telescope
    assert abs(covariance_error) <= bound
    if coupling == 1:
        assert (eF, eG, eFG, covariance_error) == (0, 0, 0, 0)
    if coupling == 2:
        assert covariance_error != 0
        print("EXACT z=2 covariance difference:", covariance_error)
        print("EXACT z=2 original three-moment upper bound:", bound)
print("PASS symbolic exact E1/F19 3-moment covariance telescope")
print("PASS 4/4 exact rational source-error upper bounds")
print("PASS z=1 bare/effective match; z=2 bare-vs-effective covariance differs")
print("SCOPE: 3-active-link Q8 conditional original Wilson slice only")
print("OPEN full SU(N) original E1 physical RG estimates, W1/W3, OS/H mass gap")
