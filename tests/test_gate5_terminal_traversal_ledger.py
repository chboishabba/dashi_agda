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
    / "GRQFTTerminalCompositionBoundary.agda"
)


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), "missing GR/QFT terminal composition boundary"
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
        rf"^{re.escape(value_name)}\s*:\s*.*?^{re.escape(value_name)}\s*=\s*\n\s*record\b.*?(?=^\S)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert match is not None, f"missing value {value_name}"
    return match.group(0)


def test_gate5_terminal_ledger_records_traversal_domain_closure_layer(
    receipt_text: str,
) -> None:
    assert (
        "postTerminalGate5HilbertStoneTraversalDomainClosureWiringLayer"
        in receipt_text
    )

    canonical_layers = re.search(
        r"^canonicalPostTerminalIntegrationLayers\s*:.*?"
        r"^canonicalPostTerminalIntegrationLayers\s*=\s*(?P<block>.*?)(?=^\S)",
        receipt_text,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert canonical_layers is not None, "missing canonical post-terminal layers"
    assert (
        "postTerminalGate5HilbertStoneTraversalDomainClosureWiringLayer"
        in canonical_layers.group("block")
    )


def test_gate5_terminal_ledger_consumes_traversal_domain_closure_wiring(
    receipt_text: str,
) -> None:
    record = record_block(receipt_text, "PostTerminalLayerIntegrationLedger")
    value = value_block(receipt_text, "canonicalPostTerminalLayerIntegrationLedger")

    for term in (
        "gate5HilbertStoneTraversalDomainClosureWiring",
        "Gate5Schrodinger.Gate5HilbertStoneTraversalDomainClosureWiring",
        "closureWiredThroughGate5Step",
        "finiteTraversalDomainClosureComposed",
        "physicalStonePromotion",
    ):
        assert term in record, term

    assert re.search(
        r";\s*gate5HilbertStoneTraversalDomainClosureWiring\s*=\s*"
        r"Gate5Schrodinger\.gate5HilbertStoneTraversalDomainClosureWiring\b",
        value,
    )
    for proof in (
        "Gate5Schrodinger.Gate5HilbertStoneTraversalDomainClosureWiring.closureWiredThroughGate5Step-v",
        "Gate5Schrodinger.Gate5HilbertStoneTraversalDomainClosureWiring.finiteTraversalDomainClosureComposed-v",
        "Gate5Schrodinger.Gate5HilbertStoneTraversalDomainClosureWiring.physicalStonePromotion-v",
    ):
        assert proof in value, proof


def test_gate5_terminal_ledger_keeps_physical_and_terminal_promotions_false(
    receipt_text: str,
) -> None:
    record = record_block(receipt_text, "PostTerminalLayerIntegrationLedger")
    value = value_block(receipt_text, "canonicalPostTerminalLayerIntegrationLedger")

    for field in (
        "gate5TraversalDomainPhysicalStonePromotionStillFalse",
        "gate5TraversalDomainPhysicalGeneratorPromotionStillFalse",
        "terminalClaimPromotedIsFalse",
    ):
        assert field in record, field

    assert "selfAdjointPhysicalGeneratorPromoted" in record
    assert re.search(r";\s*terminalClaimPromoted\s*=\s*false\b", value)

    forbidden_true_assignments = (
        "physicalStonePromotion",
        "selfAdjointPhysicalGeneratorPromoted",
        "terminalClaimPromoted",
    )
    for name in forbidden_true_assignments:
        assert not re.search(rf"\b{re.escape(name)}\s*=\s*true\b", value), name

    assert "physical Stone and physical generator promotion remain false" in value
    assert "terminalClaimPromoted remains false" in value
