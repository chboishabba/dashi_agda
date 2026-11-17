"""Executable finite audit for native ternary local gauge + source proof boundaries."""
import sys
from pathlib import Path
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from alexander_horned_native_ternary_local_phase_action_exact import (
    check,addresses,parent,child,pullback,rotate_back,novelty_curve,
    field_add,shift_field,semidirect_multiply,semidirect_inverse,
    semidirect_unit,
)

def test_exhaustive_eighty_one_cubed_semidirect_laws():
    result=check()
    assert result["status"]=="PASS"
    assert result["all_81_cubed_associativity_cases"]==531441
    assert result["higher_depth_group_checks"]==1200
    assert result["gauge_transitive_root_field_pairs"]==729
    assert result["address_shift_checks"]==1080
    assert result["depth_two_cells"]==27
    assert result["depth_two_local_group_size"]==7625597484987
    assert result["depth_two_semidirect_size"]==22876792454961

def test_explicit_prefix_section_and_refinement_are_injective():
    for depth in range(4):
        for x in addresses(depth):
            assert parent(child(x))==x
            for shift in (0,1,2):
                assert parent(rotate_back(child(x),shift))==rotate_back(x,shift)

def test_local_gauge_is_not_global_value_permutation():
    x,y,z=addresses(0)
    f={x:0,y:0,z:0}
    g={x:0,y:1,z:0}
    assert novelty_curve([f[x],f[y],f[z]])==(0,1,1,1)
    h=field_add(f,g)
    assert novelty_curve([h[x],h[y],h[z]])==(0,1,2,2)
    assert all(novelty_curve([(v+s)%3 for v in (f[x],f[y],f[z])])
               ==(0,1,1,1) for s in range(3))

def test_strict_depth_and_positive_prefix_gate():
    for bad in (-1,6,False,2.5):
        with pytest.raises(ValueError):
            addresses(bad)
    for x in addresses(0):
        with pytest.raises(ValueError):
            parent(x)

def test_canonical_owner_and_no_unsafe_proof_promotion():
    src=(ROOT/"DASHI/Mathematics/Topology/"
         "AlexanderHornedNativeTernaryLocalPhaseActionExact.agda").read_text()
    root=(ROOT/"DASHI/EverythingTOESymmetryResolved369.agda").read_text()
    for needed in (
        "AlexanderHornedNativeBalancedTernaryEndTowerExact",
        "FiniteC3OrbitStabilizerExact",
        "RecursiveFibreTower",
        "AlexanderHornedNativeTernaryFibreActionExact",
        "refineRotationSquare",
        "twistedAssociativeGaugeAt",
        "twistedInverseRightGaugeAt",
        "sameOnEndsRefinement",
        "sameOnEndsRotationCongruence",
        "gaugeInvariantObservableConstant",
        "tritPhaseRoundTrip",
    ):
        assert needed in src
    assert "import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryLocalPhaseActionExact" in root
    prior=(ROOT/"DASHI/Mathematics/Topology/"
           "AlexanderHornedNativeTernaryFibreActionExact.agda").read_text()
    for original in ("FibreAction","pullbackInjective","transitiveAction",
                     "refinementEvaluation"):
        assert original in prior
    assert "Fibre.FibreAction" in src and "Fibre.pullback" in src
    assert "Fibre.transitiveAction" in src
    for forbidden in ("postulate\n","{!!}", "allow-unsolved-metas",
                      "NO_POSITIVITY_CHECK","{-# TERMINATING #-}"):
        assert forbidden not in src
