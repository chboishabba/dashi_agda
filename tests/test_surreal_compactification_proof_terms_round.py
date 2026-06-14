from __future__ import annotations

import re
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]


EXPECTED_MODULES = {
    "DASHI.Foundations.SurrealCompactificationQQCarrier": {
        "path": "DASHI/Foundations/SurrealCompactificationQQCarrier.agda",
        "required": (
            "data QQCarrierScope",
            "data QQAuthorityBoundary",
            "data BoundedQQ",
            "zeroQQ",
            "oneQQ",
            "thirdQQ",
            "thirdPowerGauge",
            "data _≤QQ_",
            "record QQOrderReceipt",
            "checkedOrderReceipt",
            "gauge-step",
            "gauge-antitone",
            "record QQCarrierFailClosedFlags",
            "canonicalQQCarrierFailClosedFlags",
            "record QQCarrierSurface",
            "canonicalQQCarrierSurface",
            "surfaceDoesNotAcceptExternalQQ",
            "surfaceDoesNotAcceptExternalNo",
            "surfaceDoesNotClaimCompleteQQ",
            "surfaceDoesNotClaimCompleteNo",
        ),
        "false_assignments": (
            "externalQQOrderAuthorityAccepted",
            "externalQQCarrierAuthorityAccepted",
            "externalNoCarrierAuthorityAccepted",
            "dataRationalImported",
            "completeQQClaimed",
            "completeNoClaimed",
        ),
    },
    "DASHI.Foundations.SurrealCompactificationProofTermIndex": {
        "path": "DASHI/Foundations/SurrealCompactificationProofTermIndex.agda",
        "required": (
            "data ProofTermPayloadShape",
            "qqCarrierPayload",
            "balancedEmbeddingPayload",
            "antitoneGaugePayload",
            "kappaTailPayload",
            "canonicalPayloadShapes",
            "data RepoModuleAnchor",
            "data RepoIdentifierAnchor",
            "record ProofTermIndexRow",
            "qqCarrierIndexRow",
            "balancedEmbeddingIndexRow",
            "antitoneGaugeIndexRow",
            "kappaTailIndexRow",
            "canonicalProofTermIndexRows",
            "record ProofTermIndexSurface",
            "canonicalProofTermIndexSurface",
            "canonicalProofTermIndexFailClosed",
            "canonicalProofTermIndexDoesNotPromote",
            "canonicalProofTermIndexKappaTailFailsClosed",
            "canonicalProofTermIndexAntitoneDoesNotPromote",
            "canonicalProofTermIndexQQCarrierDoesNotPromote",
            "canonicalProofTermIndexBalancedEmbeddingDigit",
        ),
        "false_assignments": (
            "constructedHere",
            "promotedHere",
            "anyPayloadProofPromotedHere",
        ),
    },
    "DASHI.Foundations.SurrealCompactificationIntake": {
        "path": "DASHI/Foundations/SurrealCompactificationIntake.agda",
        "required": (
            "data CarrierShape",
            "qqRationalCarrier",
            "record NoQQCarrierBridgeIntake",
            "canonicalNoQQCarrierBridgeIntake",
            "data BalancedTernaryDigit",
            "balancedTernaryEmbedDigit",
            "negEmbedsToMinusOne",
            "zerEmbedsToZero",
            "posEmbedsToPlusOne",
            "record AntitoneGaugeLemmaIntake",
            "canonicalAntitoneGaugeLemmaIntake",
            "record TruncationKappaIntake",
            "canonicalTruncationKappaIntake",
            "record TailBoundIntake",
            "canonicalTailBoundIntake",
            "record ExactCheckedRationalBridgeFields",
            "canonicalExactCheckedRationalBridgeFields",
            "data ExternalAuthorityGate",
            "canonicalExternalAuthorityGates",
            "record ExternalAuthorityGateIntake",
            "canonicalExternalAuthorityGateIntake",
            "record SurrealCompactificationIntakeContract",
            "canonicalSurrealCompactificationIntakeContract",
        ),
        "false_assignments": (
            "constructedHere",
            "promotedHere",
            "extensionToQQConstructedHere",
            "rationalValueConstructedHere",
            "antitoneLemmaProvedHere",
            "truncationBoundProvedHere",
            "tailBoundProvedHere",
            "orderedQQPromotionAcceptedHere",
            "qqCarrierConstructedHere",
            "qqCarrierPromotedHere",
            "threeMinusNRationalValueConstructedHere",
            "rationalAuthorityAcceptedHere",
            "bridgePromotionAcceptedHere",
            "anyGateAcceptedHere",
            "noToQQPromoted",
            "qqToNoPromoted",
            "compactificationPromoted",
            "analyticTailBoundPromoted",
        ),
    },
    "DASHI.Foundations.SurrealCompactificationRationalBridge": {
        "path": "DASHI/Foundations/SurrealCompactificationRationalBridge.agda",
        "required": (
            "record SymbolicRationalApproximation",
            "SymbolicDenominator",
            "threePower",
            "embedTritVec",
            "towerToSymbolicRational",
            "FiniteTritTowerSymbolicRationalBridge",
            "canonicalFiniteTritTowerSymbolicRationalBridge",
            "canonicalBridgeDoesNotPromoteQQ",
            "canonicalBridgeDoesNotPromoteNo",
            "Intake.balancedTernaryEmbedDigit",
            "Intake.canonicalNoQQCarrierBridgeIntake",
        ),
        "false_assignments": (
            "qqCarrierPromoted",
            "noCarrierPromoted",
        ),
    },
    "DASHI.Foundations.SurrealCompactificationOrderedQQBridge": {
        "path": "DASHI/Foundations/SurrealCompactificationOrderedQQBridge.agda",
        "required": (
            "data QQCarrierShape",
            "symbolicOrderedQQCarrier",
            "data SymbolicOrderedQQTerm",
            "qq-from-rational-approximation",
            "data SymbolicQQOrderReceipt",
            "record OrderedQQAntitoneDependency",
            "canonicalOrderedQQAntitoneDependency",
            "record OrderedQQNonPromotionReceipts",
            "canonicalOrderedQQNonPromotionReceipts",
            "record OrderedQQBridgeSurface",
            "canonicalOrderedQQBridgeSurface",
            "canonicalOrderedBridgeConcreteQQCarrierNotPromoted",
            "canonicalOrderedBridgeConcreteQQArithmeticNotPromoted",
            "canonicalOrderedBridgeConcreteQQOrderNotPromoted",
            "canonicalOrderedBridgeAntitoneDoesNotPromoteLemma",
        ),
        "false_assignments": (
            "antitoneLemmaPromotedHere",
            "concreteQQCarrierPromoted",
            "concreteNoCarrierPromoted",
            "concreteQQArithmeticPromoted",
            "concreteQQOrderPromoted",
        ),
    },
    "DASHI.Foundations.SurrealCompactificationTailBoundBridge": {
        "path": "DASHI/Foundations/SurrealCompactificationTailBoundBridge.agda",
        "required": (
            "record GeometricSeriesTailLawShape",
            "geometric-series-tail-law",
            "record KappaTailBoundLawShape",
            "kappaTailBound-law",
            "record CompactificationTailBoundBridgeSurface",
            "canonicalCompactificationTailBoundBridgeSurface",
            "canonicalGeometricSeriesTailFailsClosed",
            "canonicalKappaTailBoundFailsClosed",
            "canonicalKappaTailBoundDoesNotPromote",
            "RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge",
            "Intake.canonicalExactCheckedRationalBridgeFields",
        ),
        "false_assignments": (
            "analyticTailBoundProvedHere",
            "analyticTailBoundPromoted",
            "kappaTailBoundProvedHere",
            "kappaTailBoundPromoted",
            "anyAnalyticProofPromotedHere",
        ),
    },
}

PROOF_TERM_INDEX_GATES = (
    "noCarrierAuthority",
    "qqCarrierAuthority",
    "qqOrderAuthority",
    "balancedTernaryToQQEmbeddingAuthority",
    "threeMinusNGaugeAuthority",
    "antitoneGaugeLemmaAuthority",
    "truncationKappaAuthority",
    "tailBoundAuthority",
)


def read_module(relative_path: str) -> str:
    path = REPO_ROOT / relative_path
    assert path.is_file(), f"missing {relative_path}"
    return path.read_text(encoding="utf-8")


def bool_field_has_false_witness(text: str, name: str) -> bool:
    return (
        re.search(rf"\b{re.escape(name)}\s*:\s*Bool\b", text) is not None
        and re.search(rf"\b{re.escape(name)}IsFalse\s*:", text) is not None
        and re.search(rf"\b{re.escape(name)}\s*≡\s*false\b", text) is not None
    )


def canonical_record_assigns_false(text: str, name: str) -> bool:
    return re.search(rf";\s*{re.escape(name)}\s*=\s*false\b", text) is not None


@pytest.mark.parametrize("module_name, spec", EXPECTED_MODULES.items())
def test_surreal_compactification_round_modules_expose_expected_identifiers(
    module_name: str,
    spec: dict[str, object],
) -> None:
    text = read_module(str(spec["path"]))

    assert re.search(rf"^module\s+{re.escape(module_name)}\s+where$", text, re.MULTILINE)
    for identifier in spec["required"]:
        assert identifier in text, identifier


@pytest.mark.parametrize("module_name, spec", EXPECTED_MODULES.items())
def test_surreal_compactification_round_promotion_fields_fail_closed(
    module_name: str,
    spec: dict[str, object],
) -> None:
    text = read_module(str(spec["path"]))

    for name in spec["false_assignments"]:
        assert bool_field_has_false_witness(text, name), f"{module_name}.{name}"
        if canonical_record_assigns_false(text, name):
            assert f"{name}IsFalse" in text


def test_surreal_compactification_proof_term_index_lists_required_authority_gates() -> None:
    text = read_module("DASHI/Foundations/SurrealCompactificationIntake.agda")
    index_block = re.search(
        r"canonicalExternalAuthorityGates\s*:\s*List\s+ExternalAuthorityGate"
        r".*?canonicalExternalAuthorityGates\s*=\s*(.*?)\s*∷\s*\[\]",
        text,
        flags=re.DOTALL,
    )
    assert index_block is not None
    index_text = index_block.group(1)

    for gate in PROOF_TERM_INDEX_GATES:
        assert gate in index_text, gate

    assert "record ExternalAuthorityGateIntake" in text
    assert "gates ≡ canonicalExternalAuthorityGates" in text
    assert "anyGateAcceptedHere ≡ false" in text


def test_surreal_compactification_proof_term_index_rows_cover_round_payloads() -> None:
    text = read_module("DASHI/Foundations/SurrealCompactificationProofTermIndex.agda")

    for payload in (
        "qqCarrierPayload",
        "balancedEmbeddingPayload",
        "antitoneGaugePayload",
        "kappaTailPayload",
    ):
        assert payload in text

    for row in (
        "qqCarrierIndexRow m n k",
        "balancedEmbeddingIndexRow m n k",
        "antitoneGaugeIndexRow m n k",
        "kappaTailIndexRow m n k",
    ):
        assert row in text

    for identifier in (
        "qqCarrierShapeIdentifier",
        "balancedTernaryEmbeddingIntakeIdentifier",
        "orderedQQAntitoneDependencyIdentifier",
        "symbolicThreeMinusNGaugeIntakeIdentifier",
        "truncationKappaIntakeIdentifier",
        "kappaTailBoundLawShapeIdentifier",
        "compactificationTailBoundBridgeSurfaceIdentifier",
    ):
        assert identifier in text

    assert "anyPayloadProofPromotedHere ≡ false" in text
    assert "allAuthorityGatesFailClosed ≡ true" in text


def test_surreal_compactification_bounded_qq_carrier_stays_builtin_only() -> None:
    text = read_module("DASHI/Foundations/SurrealCompactificationQQCarrier.agda")

    assert not re.search(r"^open\s+import\s+Data\.Rational\b", text, flags=re.MULTILINE)
    assert "data BoundedQQ" in text
    assert "data _≤QQ_" in text
    assert "gauge-antitone" in text
    assert "externalQQCarrierAuthorityAccepted ≡ false" in text
    assert "externalNoCarrierAuthorityAccepted ≡ false" in text
    assert "dataRationalImported ≡ false" in text


def test_surreal_compactification_round_keeps_concrete_qq_and_no_authority_unaccepted() -> None:
    ordered = read_module("DASHI/Foundations/SurrealCompactificationOrderedQQBridge.agda")
    intake = read_module("DASHI/Foundations/SurrealCompactificationIntake.agda")
    rational = read_module("DASHI/Foundations/SurrealCompactificationRationalBridge.agda")

    for text in (ordered, intake, rational):
        assert "canonicalNoQQCarrierBridgeIntake" in text
        assert "promoted" in text.lower()

    for identifier in (
        "NoCarrierAuthorityArtifact",
        "QQCarrierAuthorityArtifact",
        "RationalOrderAuthorityArtifact",
        "noCarrierAuthorityNotAcceptedHere",
        "qqCarrierAuthorityNotAcceptedHere",
        "rationalOrderAuthorityNotAcceptedHere",
    ):
        assert identifier in intake

    assert "qqCarrierAuthorityNotAccepted =\n        Intake.qqCarrierAuthorityNotAcceptedHere" in ordered
    assert (
        "rationalOrderAuthorityNotAccepted =\n        Intake.rationalOrderAuthorityNotAcceptedHere"
        in ordered
    )
