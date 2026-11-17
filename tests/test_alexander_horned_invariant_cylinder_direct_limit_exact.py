"""Finite original #1244 invariant cylinder / directed colimit exact regression.

No accidental global function extensionality or assumption that the direct
limit is already the FULL space of continuous C3-valued functions.
"""
import sys
from pathlib import Path
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from alexander_horned_invariant_cylinder_direct_limit_exact import (
    orbits,words,orbit,project_orbit,field,pullback,restrict_zero,
    lift_to,add,inverse,same_eventually,eval_end,check
)

def test_exact_invariant_direct_limit_finite_oracle():
    receipt=check()
    assert receipt["status"]=="PASS"
    assert receipt["ranks_by_depth"]=={
        0:1,1:2,2:5,3:14,4:41,5:122,6:365}
    assert receipt["exhaustive_invariant_fields"]==255
    assert receipt["common_depth_cases"]==2000
    assert receipt["depth2_orbit_fibre_group"]==243

def test_canonical_zero_child_retracts_exact_orbit_pullback():
    for n in range(4):
        f=field(n,[(2*i+1)%3 for i in range(len(orbits(n)))])
        assert restrict_zero(pullback(f))==f
        assert same_eventually(f,pullback(f))
        assert all(eval_end(f,tuple(w)+(0,))==
                   eval_end(pullback(f),tuple(w)+(0,))
                   for w in words(n))

def test_common_refinement_does_not_imply_original_same_depth():
    a=field(0,(2,))
    b=pullback(pullback(a))
    assert a!=b and same_eventually(a,b)
    assert same_eventually(add(a,b),field(0,(1,)))
    assert same_eventually(add(a,inverse(a)),field(0,(0,)))

def test_distinguish_original_five_from_eleven_unrelated_orbits():
    assert len(orbits(2))==5
    assert len(orbits(3))==14
    assert len(orbits(4))==41
    assert len(orbits(4))!=(3**4+1)
    assert 3**len(orbits(2))==243
    assert 3**len(orbits(2))!=5**3
    # Neither a quotient of 27 time samples nor a group isomorphism
    # to the independent #1414 5^3 three-five-mode carrier.

def test_agda_source_owner_and_kernel_boundary():
    owner=(ROOT/"DASHI/Mathematics/Topology/"
           "AlexanderHornedNativeTernaryFibreActionExact.agda").read_text()
    formal=(ROOT/"DASHI/Mathematics/Topology/"
            "AlexanderHornedInvariantCylinderDirectLimitExact.agda").read_text()
    umbrella=(ROOT/"DASHI/EverythingTOESymmetryResolved369.agda").read_text()
    assert "invariantsPullback" in owner
    for theorem in (
        "liftInvariant","commonDepth","combineCylinder",
        "combineAssociativeOnEnds","combineCongruence",
        "extendEnd","extendEndAt","sameOnEndsImpliesEventual",
        "eventualImpliesSameOnEnds","restrictInvariantToZeroChild",
        "restrictPullbackIsIdentityAt","restrictPreservesCombine"):
        assert theorem in formal
    assert "import DASHI.Mathematics.Topology.AlexanderHornedInvariantCylinderDirectLimitExact" in umbrella
    for forbidden in ("postulate\n","{!!}","allow-unsolved-metas",
                      "NO_POSITIVITY_CHECK","{-# TERMINATING #-}"):
        assert forbidden not in formal

def test_strict_finite_depth_gate():
    for invalid in (-1,8,True,2.5):
        with pytest.raises(ValueError):
            words(invalid)
    with pytest.raises(ValueError):
        project_orbit(())
    with pytest.raises(ValueError):
        restrict_zero(field(0,(0,)))
    with pytest.raises(ValueError):
        lift_to(field(2,(0,0,0,0,0)),1)
