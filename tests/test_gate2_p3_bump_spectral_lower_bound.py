from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SLICE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "PressureBelow15SpectralNatWitnessSlice.agda"
)


def read_slice() -> str:
    assert SLICE.is_file(), f"missing {SLICE.relative_to(REPO_ROOT)}"
    return SLICE.read_text(encoding="utf-8", errors="replace")


def block_between(text: str, start: str, end: str) -> str:
    start_index = text.index(start)
    end_index = text.index(end, start_index)
    return text[start_index:end_index]


def assigned(block: str, field_name: str, value: str) -> bool:
    return bool(
        re.search(
            rf"[;{{]\s*{re.escape(field_name)}\s*=\s*{re.escape(value)}\b",
            block,
            flags=re.DOTALL,
        )
    )


def test_p3_bump_surface_exposes_concrete_nat_lower_bound_fields() -> None:
    text = read_slice()

    record_block = block_between(
        text,
        "record S8NatP3BumpFiniteSpectralLowerBoundSurface : Set",
        "open S8NatP3BumpFiniteSpectralLowerBoundSurface public",
    )

    for term in (
        "witnessStateIsP3Bump",
        "p3LaneOccupation",
        "p5LaneOccupation",
        "p7LaneOccupation",
        "p3LaneHamiltonian",
        "p5LaneHamiltonian",
        "p7LaneHamiltonian",
        "activeLaneHamiltonianSum",
        "globalHamiltonian",
        "pressureNorm",
        "selectedPositiveLowerBound",
        "subThresholdLowerBoundAtWitness",
        "spectralGapPromoted",
        "spectralGapPromotedIsFalse",
        "spectralGapPromoted",
        "false",
        "continuumClayMassGapPromoted",
        "continuumClayMassGapPromotedIsFalse",
        "continuumClayMassGapPromoted",
        "false",
    ):
        assert term in record_block, term


def test_p3_bump_arithmetic_equalities_are_wired_to_canonical_surface() -> None:
    text = read_slice()

    canonical_block = block_between(
        text,
        "canonicalS8NatP3BumpFiniteSpectralLowerBoundSurface =",
        "s8NatCarrierQuotientHilbertSpace :",
    )

    expected_assignments = {
        "witnessState": "s8NatP3BumpFactorVec",
        "p3LaneOccupation": "s8NatP3BumpP3LaneOccupationIs1",
        "p5LaneOccupation": "s8NatP3BumpP5LaneOccupationIs0",
        "p7LaneOccupation": "s8NatP3BumpP7LaneOccupationIs0",
        "p3LaneHamiltonian": "s8NatP3BumpP3LaneHamiltonianIs3",
        "p5LaneHamiltonian": "s8NatP3BumpP5LaneHamiltonianIs0",
        "p7LaneHamiltonian": "s8NatP3BumpP7LaneHamiltonianIs0",
        "activeLaneHamiltonianSum": "s8NatP3BumpActiveLaneHamiltonianSumIs3",
        "globalHamiltonian": "s8NatP3BumpHamiltonianIs3",
        "selectedPositiveLowerBound": "s8NatOne",
        "spectralGapPromoted": "false",
        "continuumClayMassGapPromoted": "false",
    }

    for field_name, value in expected_assignments.items():
        assert assigned(canonical_block, field_name, value), f"{field_name} = {value}"

    for fact in (
        "s8NatP3BumpHamiltonianIs3",
        "s8NatP3BumpP3LaneOccupationIs1",
        "s8NatP3BumpP5LaneOccupationIs0",
        "s8NatP3BumpP7LaneOccupationIs0",
        "s8NatP3BumpP3LaneHamiltonianIs3",
        "s8NatP3BumpP5LaneHamiltonianIs0",
        "s8NatP3BumpP7LaneHamiltonianIs0",
        "s8NatP3BumpActiveLaneHamiltonianSumIs3",
    ):
        assert fact in text, fact


def test_lower_bound_routes_through_subthreshold_and_stays_non_promoting() -> None:
    text = read_slice()

    canonical_block = block_between(
        text,
        "canonicalS8NatP3BumpFiniteSpectralLowerBoundSurface =",
        "s8NatCarrierQuotientHilbertSpace :",
    )
    bridge_block = block_between(
        text,
        "canonicalS8NatToGlobalSpectralGapPromotionBridge =",
        "data S8NatGlobalCarrierSelfAdjointFieldProgressVerdict",
    )

    assert "s8NatSubThresholdLowerBound" in canonical_block
    assert "Probe.fourteenBelowFifteen" in canonical_block
    assert "s8NatP3BumpFactorVec" in canonical_block
    assert "p3BumpNonVacuum" in canonical_block
    assert "p3BumpOrthogonal" in canonical_block
    assert "1 <= H(p3-bump) = 3" in canonical_block

    assert assigned(bridge_block, "gapReceiptConstructed", "false")
    assert assigned(bridge_block, "spectralGapPromoted", "false")
    assert assigned(bridge_block, "terminalClaimPromoted", "false")
    assert assigned(bridge_block, "continuumClayMassGapPromoted", "false")
    assert "gapReceiptOnlyFromInhabitedS8Theorem" in bridge_block
    assert "No spectral-gap receipt" in bridge_block
    assert "continuum Clay mass-gap promotion" in bridge_block
