#!/usr/bin/env python3
"""B4 scalar obstruction / falsifier for unqualified absorption statements.

The exact bipartite covariance alone cannot imply
 -C <= theta*Mcore + c*ED for fixed theta,c, unless the
physical structure bounds rates, work and energies together.
These examples vary a noncore rate while keeping declared scalar
budgets fixed. They are NOT realizable-NS counterexamples.
"""
from fractions import Fraction as Q
from ns_b4_r440_oscillation_bound import covariance

def scalar_obstruction(scale: int, theta=Q(1, 4), c=Q(1)):
    if scale < 1:
        raise ValueError("scale must be positive")
    # Noncore rate larger than core rate, coherent work difference negative:
    # C=(scale-0)*(0-1)=-scale so physical defect -C=scale.
    noncore=((Q(scale), Q(0)),)
    core=((Q(0), Q(1)),)
    signed_defect=-covariance(noncore,core)
    # Formal scalar placeholders only: without a physical compatibility
    # relation there is no mechanism tying them to signed work.
    core_mass=Q(1)
    local_ed=Q(1)
    allowance=theta*core_mass+c*local_ed
    return {
        "scale":scale,
        "signed_defect":str(signed_defect),
        "allowance":str(allowance),
        "violates_unqualified_absorption":signed_defect>allowance,
        "physical_NS_realizability":"not_asserted",
        "meaning":"independence of covariance algebra from coercive physical energy control",
    }

def minimal_violation(theta=Q(1,4),c=Q(1)):
    if theta<0 or c<0 or theta>=Q(1,2):
        raise ValueError("expect positive strict-margin candidate")
    scale=int(theta+c)+1
    return scalar_obstruction(scale,theta,c)

if __name__=="__main__":
    print(minimal_violation())
