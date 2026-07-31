#!/usr/bin/env python3
"""Fail-closed static audit for the focused UBP epistemic/lattice tranche."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

FOCUSED_FILES = {
    "DASHI/Foundations/UBP/SourceAtlas.agda": (
        "module DASHI.Foundations.UBP.SourceAtlas where",
        "10.1017/S0305004100052075",
        "10.4153/CJM-1967-017-0",
        "10.1007/978-1-4757-6568-7",
        "10.1109/18.312154",
        "10.1109/TC.2008.213",
        "10.4007/annals.2017.185.3.8",
        "canonicalUBPSourceCountIsSeven",
        "canonicalUBPSourceReceiptNonPromoting",
    ),
    "DASHI/Foundations/UBP/ExactnessAndLatticeBoundary.agda": (
        "module DASHI.Foundations.UBP.ExactnessAndLatticeBoundary where",
        "rationalFractionCannotEqualExactObserverConstant",
        "RationalIntervalCertificate",
        "bitAddressNormSquaredIs16",
        "leechHasNoIntegerNormSquared16",
        "bitAddressIsNotLeechMember",
        "LeechMembershipCertificate",
        "fullGolayParityGlueCertificateRequired",
        "ubpExactnessAndLatticeReceiptNonPromoting",
    ),
    "DASHI/Foundations/UBP/RepresentationAndObserverBoundary.agda": (
        "module DASHI.Foundations.UBP.RepresentationAndObserverBoundary where",
        "shadowPreimageCountIsSixtyFourTimesGolayCount",
        "checkAloneProvesEquivalenceIsFalse",
        "M24EquivarianceRequiredIsTrue",
        "SemanticMetricBridge",
        "trajectoryObserversDiffer",
        "SpatialProjectionLaw",
        "genuineLeechToThreeDimensionalProjectionSuppliedIsFalse",
        "representationAndObserverReceiptNonPromoting",
    ),
    "DASHI/Foundations/UBP/EvidenceInterpretationLedger.agda": (
        "module DASHI.Foundations.UBP.EvidenceInterpretationLedger where",
        "standardTheorem",
        "implementationVerified",
        "ubpDefinition",
        "derivedInternalTheorem",
        "empiricalFit",
        "outOfSamplePrediction",
        "interpretiveConjecture",
        "formalGap",
        "InterpretationBridge",
        "canonicalUBPClaimRowsNonPromoting",
        "externalReplicationSuppliedIsFalse",
        "ubpInterpretationGenericReceiptNonPromoting",
    ),
    "DASHI/Foundations/UBP/Regression.agda": (
        "module DASHI.Foundations.UBP.Regression where",
        "sourceCountRegression",
        "claimRowCountRegression",
        "shadowCardinalityRegression",
        "observerConstantFractionClaimClosed",
        "ambientAddressMembershipClaimClosed",
        "mogEquivalenceClaimClosed",
        "coordinateMassMeaningClosed",
        "graySemanticAutomaticityClosed",
        "leechToThreeDimensionalProjectionClaimClosed",
        "externalReplicationClaimClosed",
        "allFocusedReceiptsRemainNonPromoting",
    ),
}

SUPPORT_FILES = {
    "Docs/support/reference/UBPEpistemicLatticeBoundary.md": (
        "# UBP epistemic and Leech-lattice boundary",
        "## Remaining frontier",
        "10.1109/TC.2008.213",
    ),
    ".github/workflows/ubp-epistemic-lattice-boundary.yml": (
        "check_ubp_epistemic_lattice_boundary.py",
        "DASHI/Foundations/UBP/Regression.agda",
    ),
}

FORBIDDEN_AGDA_TOKENS = (
    "postulate",
    "{!!}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
    "{-# NO_POSITIVITY_CHECK #-}",
    "{-# NO_UNIVERSE_CHECK #-}",
)

FORBIDDEN_PROMOTION_PHRASES = (
    "externalVerificationSuppliedIsTrue",
    "scientificAuthorityPromotedIsTrue",
    "physicalAuthorityPromotedIsTrue",
    "semanticAuthorityPromotedIsTrue",
    "exactIrrationalTargetRepresentedByFractionIsTrue",
    "individualAddressMembershipClaimIsTrue",
    "checkAloneProvesEquivalenceIsTrue",
    "genuineLeechToThreeDimensionalProjectionSuppliedIsTrue",
)


def fail(message: str) -> None:
    print(f"UBP boundary audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def require_file(relative: str, tokens: tuple[str, ...], *, agda: bool) -> str:
    path = ROOT / relative
    if not path.is_file():
        fail(f"missing required file {relative}")
    text = path.read_text(encoding="utf-8")
    for token in tokens:
        if token not in text:
            fail(f"{relative} is missing required token {token!r}")
    if agda:
        for token in FORBIDDEN_AGDA_TOKENS:
            if token in text:
                fail(f"{relative} contains forbidden Agda token {token!r}")
        for phrase in FORBIDDEN_PROMOTION_PHRASES:
            if phrase in text:
                fail(f"{relative} contains forbidden promotion phrase {phrase!r}")
    return text


def main() -> None:
    agda_text = {
        relative: require_file(relative, tokens, agda=True)
        for relative, tokens in FOCUSED_FILES.items()
    }
    for relative, tokens in SUPPORT_FILES.items():
        require_file(relative, tokens, agda=False)

    source = agda_text["DASHI/Foundations/UBP/SourceAtlas.agda"]
    if source.count("sourceEntry\n") < 7:
        fail("source atlas does not visibly contain seven source entries")

    ledger = agda_text[
        "DASHI/Foundations/UBP/EvidenceInterpretationLedger.agda"
    ]
    for status in (
        "standardTheorem",
        "implementationVerified",
        "ubpDefinition",
        "derivedInternalTheorem",
        "empiricalFit",
        "outOfSamplePrediction",
        "interpretiveConjecture",
        "formalGap",
    ):
        if ledger.count(status) < 2:
            fail(f"claim status {status!r} is declared but not used in the ledger")

    exactness = agda_text[
        "DASHI/Foundations/UBP/ExactnessAndLatticeBoundary.agda"
    ]
    if "exactRationalExecutionIsTrue" not in exactness:
        fail("rational exact-execution status is missing")
    if "exactIrrationalTargetRepresentedByFractionIsFalse" not in exactness:
        fail("irrational-target nonrepresentation boundary is missing")

    representation = agda_text[
        "DASHI/Foundations/UBP/RepresentationAndObserverBoundary.agda"
    ]
    for required_false in (
        "checkAloneProvesEquivalenceIsFalse",
        "intrinsicMassMeaningEstablishedIsFalse",
        "semanticEncodingConstructedByIsometryAloneIsFalse",
        "genuineLeechToThreeDimensionalProjectionSuppliedIsFalse",
        "macroscopicEmergenceTheoremEstablishedIsFalse",
    ):
        if required_false not in representation:
            fail(f"representation boundary missing {required_false}")

    print(
        "UBP epistemic/lattice static audit passed: "
        f"{len(FOCUSED_FILES)} Agda files and {len(SUPPORT_FILES)} support files checked"
    )


if __name__ == "__main__":
    main()
