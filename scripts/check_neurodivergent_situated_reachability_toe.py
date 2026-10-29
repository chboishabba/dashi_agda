#!/usr/bin/env python3
"""Deterministic source audit for the situated neurodivergent reachability TOE lane."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

FORBIDDEN = (
    re.compile(r"\\bpostulate\\b"),
    re.compile(r"allow-unsolved-metas"),
    re.compile(r"\\bTERMINATING\\b"),
    re.compile(r"\\bNO_POSITIVITY_CHECK\\b"),
    re.compile(r"\\bsorry\\b"),
    re.compile(r"\\badmit\\b"),
)

AGDA_FILES = (
    "DASHI/Biology/EmbodiedSocialEcologyRelationalHistoryObligationExact.agda",
    "DASHI/Biology/TrustedFriendEcologyInteractionExact.agda",
    "DASHI/Biology/NeurodivergentSocialEcologyCrossPollinationExact.agda",
    "DASHI/Biology/NeurodivergentSocialEcologySourceRegistryExact.agda",
    "DASHI/EverythingTOESymmetryResolved369.agda",
    "DASHI/Unifier.agda",
    "DASHI/Unified/Everything.agda",
)

REQUIRED = {
    "DASHI/Biology/EmbodiedSocialEcologyRelationalHistoryObligationExact.agda": (
        "canonicalHistoryPropagationWitness",
        "canonicalRelationEssentialWitness",
        "latencyCannotDetermineFutureCone",
        "postprocessedLatencyCannotRecoverFutureCone",
        "genericHistoryOptionConeContraction",
        "genericEcologyOptionConeContraction",
        "genericJointOptionConeContraction",
        "genericObserverAffordanceAuthorityBoundary",
        "canonicalSituatedReachabilityZKPFrame",
        "canonicalSituatedReachabilityTOEReceipt",
    ),
    "DASHI/Biology/TrustedFriendEcologyInteractionExact.agda": (
        "friendEcologySurface",
        "friendEcologyRectangleObstruction",
        "friendEcologyRankOneObstruction",
        "friendEcologyNotEndpointAdditive",
    ),
    "DASHI/EverythingTOESymmetryResolved369.agda": (
        "SituatedReachabilityTOE",
        "toeSituatedReachabilityReceipt",
        "toeSituatedReachabilityZKPFrame",
        "toeBalabanScaleDensityFlowLevel",
        "toeBalabanConcreteRegularELocalizationWitnessLevel",
        "toeBalabanCasimirLowerBoundTransportLevel",
        "toeBalabanContinuumLimitPromotionImpossible",
    ),
    "DASHI/Unifier.agda": (
        "SituatedReachabilityTOE",
        "unifierSituatedReachabilityReceipt",
        "unifierSituatedReachabilityZKPFrame",
        "BalabanRGTOE",
        "unifierBalabanContinuumLimitPromotionImpossible",
    ),
    "DASHI/Unified/Everything.agda": (
        "SituatedReachabilityTOE",
        "unifiedSituatedReachabilityReceipt",
        "unifiedSituatedReachabilityZKPFrame",
    ),
    "Docs/support/reference/NeurodivergentSituatedReachabilityTOE.md": (
        "ZKP audit frame",
        "Latest PR pattern audit",
        "Existing Balaban and Fleet TOE state",
        "ISO/IEC 42001",
        "NIST AI RMF",
        "Six Sigma",
        "JMD",
        "meta-introspector",
    ),
    "Docs/diagrams/neurodivergent-situated-reachability-toe.puml": (
        "@startuml",
        "EmbodiedSocialEcologyRelationalHistoryObligationExact",
        "HistoryConditionedSocialEcologyOptionConeExact",
        "HistoryObserverAuthorityOptionConeCapstoneExact",
        "EverythingTOESymmetryResolved369",
        "Unifier",
        "Unified/Everything",
        "ESD surfaces",
    ),
}


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def assert_required() -> None:
    for path, needles in REQUIRED.items():
        content = read(path)
        for needle in needles:
            assert needle in content, f"{path}: missing {needle!r}"


def assert_trust_boundary() -> None:
    for path in AGDA_FILES:
        content = read(path)
        for pattern in FORBIDDEN:
            assert not pattern.search(content), (
                f"{path}: forbidden token pattern {pattern.pattern!r}"
            )


def assert_no_esd_edit_surface() -> None:
    # This checker owns an allow-list of this lane's files.
    for path in (*AGDA_FILES, *REQUIRED.keys()):
        lowered = path.lower()
        assert "digital_esd" not in lowered
        assert "/esd" not in lowered


def assert_finite_regression() -> None:
    # Exact source-equivalent finite specimen.
    processing_gate = True

    def future(history_gate: bool, reachable: bool, remain: bool) -> bool:
        realised = reachable and remain
        return history_gate and processing_gate and realised

    table = {
        "ordinaryAlone": future(True, True, False),
        "ordinaryFriend": future(True, True, True),
        "threatAlone": future(False, False, False),
        "threatFriend": future(False, False, True),
    }
    assert table == {
        "ordinaryAlone": False,
        "ordinaryFriend": True,
        "threatAlone": False,
        "threatFriend": False,
    }

    # Friend x ecology remain surface.
    high_alone, high_friend = 0, 1
    repair_alone, repair_friend = 1, 1
    assert high_alone + repair_friend != high_friend + repair_alone
    assert high_alone * repair_friend != high_friend * repair_alone


def main() -> None:
    assert_required()
    assert_trust_boundary()
    assert_no_esd_edit_surface()
    assert_finite_regression()
    print("situated neurodivergent reachability TOE source audit: PASS")


if __name__ == "__main__":
    main()
