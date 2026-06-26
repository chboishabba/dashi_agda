from __future__ import annotations

import re
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
BOUNDARY = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSWhitneyFubiniDisintegrationBoundary.agda"
)
COMPOSITE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSA4SardFubiniCompositeBoundary.agda"
)


@pytest.fixture(scope="module")
def boundary_text() -> str:
    return BOUNDARY.read_text(encoding="utf-8")


def block_between(text: str, start: str, end: str) -> str:
    match = re.search(
        rf"{re.escape(start)}(?P<body>.*?){re.escape(end)}",
        text,
        flags=re.DOTALL,
    )
    assert match is not None, f"missing block from {start!r} to {end!r}"
    return match.group("body")


def block_after(text: str, start: str) -> str:
    assert start in text, f"missing block start {start!r}"
    return text.split(start, 1)[1]


def field_is_false(record_block: str, field_name: str) -> bool:
    return (
        re.search(
            rf";\s*{re.escape(field_name)}\s*=\s*false\b",
            record_block,
            flags=re.DOTALL,
        )
        is not None
    )


def top_level_bool_is_false(text: str, name: str) -> bool:
    return (
        re.search(
            rf"^{re.escape(name)}\s*:\s*Bool\s*^{re.escape(name)}\s*=\s*^\s*false\b",
            text,
            flags=re.DOTALL | re.MULTILINE,
        )
        is not None
    )


def test_boundary_records_finite_whitney_fubini_consumer_law(
    boundary_text: str,
) -> None:
    for term in (
        "record FiniteWhitneyFubiniConsumerLaw",
        "canonicalFiniteWhitneyFubiniConsumerLaw",
        "finiteWhitneyFubiniConsumerLawRecorded : Bool",
        "recordsFiniteWhitneyFubiniConsumerLaw",
        "finiteConsumerLaw :\n      FiniteWhitneyFubiniConsumerLaw",
        "finiteConsumerLawIsCanonical :",
        "finiteConsumerLawFlag :",
    ):
        assert term in boundary_text, term


def test_boundary_records_exact_seven_step_finite_consumer_trace(
    boundary_text: str,
) -> None:
    expected_steps = (
        "usePhysicalProductMeasureStep",
        "useWhitneyPacketPartitionStep",
        "useBoundedOverlapStep",
        "usePhysicalPacketDisintegrationStep",
        "useFourierOutputPacketDisintegrationStep",
        "useExceptionalRoutingAndAbelCompatibilityStep",
        "consumeOutputSupportLowerBoundStep",
    )

    step_data = block_between(
        boundary_text,
        "data WhitneyFubiniFiniteConsumerStep : Set where",
        "canonicalWhitneyFubiniFiniteConsumerSteps :",
    )
    canonical_steps = block_between(
        boundary_text,
        "canonicalWhitneyFubiniFiniteConsumerSteps =",
        "whitneyFubiniFiniteConsumerStepCount : Nat",
    )

    for step in expected_steps:
        assert step in step_data, step
        assert step in canonical_steps, step

    assert canonical_steps.count("∷") == 7
    assert "whitneyFubiniFiniteConsumerStepCountIs7" in boundary_text
    assert "whitneyFubiniFiniteConsumerStepCount ≡ 7" in boundary_text
    assert "stepCount :\n      whitneyFubiniFiniteConsumerStepCount ≡ 7" in boundary_text


def test_boundary_narrows_to_missing_output_support_consumer_and_stays_closed(
    boundary_text: str,
) -> None:
    blocker_data = block_between(
        boundary_text,
        "data WhitneyFubiniDisintegrationBlocker : Set where",
        "canonicalWhitneyFubiniDisintegrationBlockers :",
    )
    finite_law = block_between(
        boundary_text,
        "record FiniteWhitneyFubiniConsumerLaw : Set where",
        "canonicalFiniteWhitneyFubiniConsumerLaw :",
    )
    canonical_law = block_between(
        boundary_text,
        "canonicalFiniteWhitneyFubiniConsumerLaw =",
        "data WhitneyFubiniDisintegrationStatusRow : Set where",
    )
    receipt = block_after(
        boundary_text,
        "canonicalNSWhitneyFubiniDisintegrationBoundary =",
    )

    for block in (blocker_data, finite_law, canonical_law):
        assert "missingOutputSupportLowerBoundConsumption" in block

    for term in (
        "lowerBoundConsumer :\n      OutputSupportLowerBoundConsumer",
        "lowerBoundConsumerIsCanonical :",
        "narrowedBlocker :\n      WhitneyFubiniDisintegrationBlocker",
        "narrowedBlockerIsOutputSupportConsumer :",
    ):
        assert term in finite_law, term

    assert "; lowerBoundConsumer =\n        canonicalOutputSupportLowerBoundConsumer" in canonical_law
    assert "; narrowedBlocker =\n        missingOutputSupportLowerBoundConsumption" in canonical_law
    assert "outputSupportLowerBoundConsumed : Bool\noutputSupportLowerBoundConsumed =\n  false" in boundary_text

    for field_name in (
        "measurablePacketAtlasStillFalse",
        "boundedOverlapSummabilityStillFalse",
        "exceptionalSetDiscardStillFalse",
        "AbelCompatibilityStillFalse",
        "FubiniDisintegrationStillFalse",
        "outputSupportConsumerStillFalse",
        "A4WhitneyCouplingStillFalse",
        "A4FourierOutputCouplingStillFalse",
        "leakageIdentityStillFalse",
        "claySolvedStillFalse",
        "clayPromotionStillFalse",
        "terminalPromotionStillFalse",
    ):
        assert field_name in receipt, field_name

    for field_name in (
        "fullClayNSSolved",
        "clayNavierStokesPromoted",
        "terminalPromotion",
    ):
        assert top_level_bool_is_false(boundary_text, field_name), field_name


def test_composite_consumes_finite_whitney_fubini_law_if_present() -> None:
    if not COMPOSITE.exists():
        pytest.skip("NSA4 Sard/Fubini composite is not present")

    composite_text = COMPOSITE.read_text(encoding="utf-8")
    if "Fubini.FiniteWhitneyFubiniConsumerLaw" not in composite_text:
        pytest.skip("finite Whitney/Fubini consumer law is not wired into composite")

    for term in (
        "import DASHI.Physics.Closure.NSWhitneyFubiniDisintegrationBoundary",
        "fubiniFiniteConsumerLaw :\n      Fubini.FiniteWhitneyFubiniConsumerLaw",
        "Fubini.canonicalFiniteWhitneyFubiniConsumerLaw",
        "finiteWhitneyFubiniConsumerLawConsumedByA4Composite : Bool",
        "finiteWhitneyFubiniConsumerLawConsumedByA4Composite =\n  true",
        "recordsFiniteWhitneyFubiniConsumerLawConsumption",
        "finiteConsumerLawConsumed :",
        "Fubini.finiteWhitneyFubiniConsumerLawRecorded ≡ true",
        "Fubini.outputSupportLowerBoundConsumed ≡ false",
    ):
        assert term in composite_text, term
