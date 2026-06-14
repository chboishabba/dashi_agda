from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "CarrierToPhysicsInterpretationFunctor.agda"
)


def read_receipt() -> str:
    assert RECEIPT.is_file(), f"missing {RECEIPT.relative_to(REPO_ROOT)}"
    return RECEIPT.read_text(encoding="utf-8", errors="replace")


def block_between(text: str, start: str, end: str) -> str:
    start_index = text.index(start)
    end_index = text.index(end, start_index)
    return text[start_index:end_index]


def assigned(block: str, field_name: str, value: str) -> bool:
    return bool(
        re.search(
            rf";\s*{re.escape(field_name)}\s*=\s*{re.escape(value)}\b",
            block,
        )
    )


def test_gate1_finite_dhr_compatibility_narrowing_stays_finite_only() -> None:
    text = read_receipt()

    record_block = block_between(
        text,
        "record FinitePrimeLaneDHRSectorCompatibilityNarrowingReceipt : Setω where",
        "canonicalFinitePrimeLaneDHRSectorCompatibilityNarrowingReceipt :",
    )
    canonical_block = block_between(
        text,
        "canonicalFinitePrimeLaneDHRSectorCompatibilityNarrowingReceipt =",
        "record PrimeLaneRepresentationSemanticsReceipt : Setω where",
    )

    assert "FinitePrimeLaneDHRSectorCompatibilityNarrowingReceipt" in record_block
    assert "finitePrimeLaneDHRCompatibilityNarrowed :" in record_block
    assert "finitePrimeLaneDHRCompatibilityNarrowed ≡ true" in record_block
    assert assigned(canonical_block, "finitePrimeLaneDHRCompatibilityNarrowed", "true")

    for field_name in (
        "arbitrarySectorCompatibilityPromoted",
        "gDHRStandardModelMatchClaimed",
    ):
        assert f"{field_name} :" in record_block
        assert f"{field_name}IsFalse :" in record_block
        assert f"{field_name} ≡ false" in record_block
        assert assigned(canonical_block, field_name, "false")


def test_gate1_dhr_arbitrary_sector_compatibility_still_names_missing_witness() -> None:
    text = read_receipt()

    dhr_law_block = block_between(
        text,
        "record DHRSectorCompatibilityLawReceipt : Setω where",
        "record CarrierToPhysicsFunctorLawReceiptSurface : Setω where",
    )
    frontier_block = block_between(
        text,
        "canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt =",
        "gate1FilteredColimitDHRSMMatchResidualFrontierNotClaimedAtFrontier :",
    )

    assert "missingDHRSectorCompatibilityPrimitiveWitness" in dhr_law_block
    assert assigned(dhr_law_block, "arbitrarySectorCompatibilityPromoted", "false")
    assert "missingDHRSectorCompatibilityPrimitiveWitness" in frontier_block
    assert assigned(frontier_block, "gDHRStandardModelMatchClaimed", "false")
