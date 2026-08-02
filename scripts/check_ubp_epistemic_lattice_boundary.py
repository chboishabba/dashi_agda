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
        "https://oeis.org/A001203",
        "canonicalUBPSourceCountIsEight",
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
    "DASHI/Foundations/UBP/Pi50ConvergentTable.agda": (
        "module DASHI.Foundations.UBP.Pi50ConvergentTable where",
        "sourceFirst50",
        "canonicalPiFirst50",
        "first47CoefficientsAgree",
        "sourceCoefficient48IsSix",
        "canonicalCoefficient48IsTwo",
        "coefficient48Mismatch",
        "sourceP50Exact",
        "canonicalP50Exact",
        "canonicalQ50Exact",
        "canonicalErrorBoundDenominatorExact",
        "sourceTableIsCanonicalPiCFThrough50IsFalse",
        "eightyDecimalDigitAccuracyEstablishedIsFalse",
        "pi50GenericReceiptNonPromoting",
    ),
    "DASHI/Foundations/UBP/ObservableAlgebraBoundary.agda": (
        "module DASHI.Foundations.UBP.ObservableAlgebraBoundary where",
        "activationDifferenceIdentity",
        "deexcitationDifferenceIdentity",
        "longCycleCancellationIdentity",
        "nrciAtTaxTen",
        "independentlyEmergentPhysicalThresholdEstablishedIsFalse",
        "endpointTaxExtensional",
        "observableAlgebraReceiptNonPromoting",
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
        "activationDifferenceRegression",
        "longCycleCancellationRegression",
        "nrciHalfThresholdRegression",
        "nrciPhysicalEmergenceClaimClosed",
        "mogEquivalenceClaimClosed",
        "coordinateMassMeaningClosed",
        "graySemanticAutomaticityClosed",
        "leechToThreeDimensionalProjectionClaimClosed",
        "externalReplicationClaimClosed",
        "sourcePiTableCanonicalClaimClosed",
        "sourcePiCoefficient48Regression",
        "canonicalPiCoefficient48Regression",
        "sourceP50Regression",
        "canonicalP50Regression",
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
    "independentlyEmergentPhysicalThresholdEstablishedIsTrue",
    "sourceTableIsCanonicalPiCFThrough50IsTrue",
    "eightyDecimalDigitAccuracyEstablishedIsTrue",
)


def fail(message: str) -> None:
    print(f"UBP boundary audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def strip_agda_comments(text: str) -> str:
    """Remove line and nested block comments before escape-token scanning."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "{-":
                block_depth += 1
                index += 2
                continue
            if pair == "-}":
                block_depth -= 1
                index += 2
                continue
            index += 1
            continue
        if not in_string and pair == "{-":
            block_depth = 1
            index += 2
            continue
        if not in_string and pair == "--":
            newline = text.find("\n", index)
            if newline == -1:
                break
            output.append("\n")
            index = newline + 1
            continue
        if char == '"' and (index == 0 or text[index - 1] != "\\"):
            in_string = not in_string
        output.append(char)
        index += 1
    if block_depth:
        fail("unterminated Agda block comment in focused source")
    return "".join(output)


def require_file(relative: str, tokens: tuple[str, ...], *, agda: bool) -> str:
    path = ROOT / relative
    if not path.is_file():
        fail(f"missing required file {relative}")
    text = path.read_text(encoding="utf-8")
    for token in tokens:
        if token not in text:
            fail(f"{relative} is missing required token {token!r}")
    if agda:
        code = strip_agda_comments(text)
        for token in FORBIDDEN_AGDA_TOKENS:
            if token in code:
                fail(f"{relative} contains forbidden Agda token {token!r}")
        for phrase in FORBIDDEN_PROMOTION_PHRASES:
            if phrase in code:
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
    if source.count("sourceEntry\n") < 8:
        fail("source atlas does not visibly contain eight source entries")

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

    pi50 = agda_text["DASHI/Foundations/UBP/Pi50ConvergentTable.agda"]
    if "sourceCoefficient48 = 6" not in pi50:
        fail("attributed source coefficient 48 is not fixed to 6")
    if "canonicalCoefficient48 = 2" not in pi50:
        fail("canonical coefficient 48 is not fixed to 2")
    if "sourceTableIsCanonicalPiCFThrough50IsFalse" not in pi50:
        fail("source/canonical continued-fraction distinction is not fail-closed")

    algebra = agda_text[
        "DASHI/Foundations/UBP/ObservableAlgebraBoundary.agda"
    ]
    for theorem in (
        "activationDifferenceIdentity",
        "deexcitationDifferenceIdentity",
        "longCycleCancellationIdentity",
        "nrciAtTaxTen",
        "endpointTaxExtensional",
    ):
        if theorem not in algebra:
            fail(f"observable algebra missing theorem {theorem}")

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
