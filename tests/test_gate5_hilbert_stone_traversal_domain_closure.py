from __future__ import annotations

import re
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "SchrodingerSelfAdjointEvolutionReceipt.agda"
)


@pytest.fixture(scope="module")
def receipt_text() -> str:
    return RECEIPT.read_text(encoding="utf-8")


def record_block(text: str, record_name: str) -> str:
    match = re.search(
        rf"record\s+{re.escape(record_name)}\b.*?(?=^open\s+{re.escape(record_name)}\s+public)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"missing record {record_name}"
    return match.group(0)


def value_block(text: str, value_name: str) -> str:
    match = re.search(
        rf"^{re.escape(value_name)}\s*=\s*\n\s*record\b.*?(?=^\S)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"missing value {value_name}"
    return match.group(0)


def field_assignment(block: str, name: str, value: str) -> None:
    assert re.search(
        rf";\s*{re.escape(name)}\s*=\s*{re.escape(value)}\b",
        block,
    ), f"missing {name} = {value}"


def test_gate5_wiring_record_exposes_traversal_inverse_domain_and_stone_laws(
    receipt_text: str,
) -> None:
    block = record_block(receipt_text, "Gate5HilbertStoneTraversalDomainClosureWiring")

    for term in (
        "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure",
        "carrierStepForwardReverseInverse",
        "carrierStepReverseForwardInverse",
        "carrierStepDomainClosedUnderForward",
        "carrierStepDomainClosedUnderReverse",
        "finiteTraversalDomainClosureComposed",
        "Stone.StoneSelfAdjoint",
        "physicalStonePromotion",
        "physicalStonePromotion-v",
        "physicalStonePromotion ≡ false",
    ):
        assert term in block, term


def test_gate5_wiring_value_forwards_closure_laws_from_selected_receipt(
    receipt_text: str,
) -> None:
    block = value_block(receipt_text, "gate5HilbertStoneTraversalDomainClosureWiring")

    for source_law in (
        "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.forwardReverseInverse",
        "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.reverseForwardInverse",
        "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.depthGeneratorSelfAdjoint",
        "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainClosedUnderForward",
        "SelectedFiniteQuotientReversibleTraversalSelfAdjointDomainClosure.generatorDomainClosedUnderReverse",
    ):
        assert source_law in block, source_law

    field_assignment(block, "closureWiredThroughGate5Step", "true")
    field_assignment(block, "finiteTraversalDomainClosureComposed", "true")
    field_assignment(block, "physicalStonePromotion", "false")


def test_final_receipt_exports_gate5_wiring_without_physical_stone_promotion(
    receipt_text: str,
) -> None:
    assert re.search(
        r"gate5HilbertStoneTraversalDomainClosureWiringReceipt\s*:\s*"
        r"Gate5HilbertStoneTraversalDomainClosureWiring",
        receipt_text,
    )
    assert re.search(
        r";\s*gate5HilbertStoneTraversalDomainClosureWiringReceipt\s*=\s*"
        r"gate5HilbertStoneTraversalDomainClosureWiring\b",
        receipt_text,
    )
    assert '"physicalStonePromotion remains false"' in receipt_text
