#!/usr/bin/env python3
"""Static fail-closed audit for the exceptional Mathieu/real-backend frontier."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED_FILES = (
    "DASHI/Foundations/FiniteLinear/F3Subspace.agda",
    "DASHI/Foundations/FiniteLinear/AntiDiagonalKernel.agda",
    "DASHI/Foundations/FiniteLinear/Regression.agda",
    "DASHI/Physics/Closure/NSTriadKNFiniteIncidenceSubspaceAdapter.agda",
    "DASHI/Foundations/TernaryGolay/MathieuSourceAtlas.agda",
    "DASHI/Foundations/TernaryGolay/CompleteWeightEnumerator.agda",
    "DASHI/Foundations/TernaryGolay/PuncturedPerfectCode.agda",
    "DASHI/Foundations/TernaryGolay/SelfDualityFiniteBoundary.agda",
    "DASHI/Foundations/TernaryGolay/GolaySelfDualSubspace.agda",
    "DASHI/Foundations/TernaryGolay/MathieuPresentationAction.agda",
    "DASHI/Foundations/TernaryGolay/MathieuStabilizerChain.agda",
    "DASHI/Foundations/TernaryGolay/FrontierRegression.agda",
    "DASHI/Foundations/UBP/ExactRealSourceAtlas.agda",
    "DASHI/Foundations/UBP/ObserverConstantProvenance.agda",
    "DASHI/Foundations/UBP/ExactRealBackendBoundary.agda",
    "DASHI/Foundations/UBP/BishopAbsMigrationReceipt.agda",
    "DASHI/Foundations/UBP/RationalCertificateTransport.agda",
    "DASHI/Foundations/UBP/TaxFiniteDynamicsBoundary.agda",
    "DASHI/Foundations/UBP/FrontierRegression.agda",
    "DASHI/Analysis/CubicalHoTTRealBackendBoundary.agda",
    "Docs/support/reference/ExceptionalMathieuAndRealBackendFrontier.md",
    "scripts/check_explicit_ternary_golay.py",
    "scripts/check_finite_subspace_self_duality.py",
)

REQUIRED_TEXT = {
    "DASHI/Foundations/FiniteLinear/F3Subspace.agda": (
        "record F3Subspace",
        "record F3LinearMap",
        "imageSubspace",
        "kernel",
        "selfDualFromInclusions",
    ),
    "DASHI/Foundations/FiniteLinear/AntiDiagonalKernel.agda": (
        "sumZeroLine",
        "antiDiagonalLine",
        "sumZeroIsAntiDiagonal",
    ),
    "DASHI/Foundations/FiniteLinear/Regression.agda": (
        "antiDiagonalKernelImageRegression",
        "nsFiniteEdgeKernelImageRegression",
        "physicalGramPromotionClosed",
    ),
    "DASHI/Physics/Closure/NSTriadKNFiniteIncidenceSubspaceAdapter.agda": (
        "NSTriadKNExactPairIncidenceGramAssembly",
        "orientedPairEdgeHasZeroSum",
        "finitePairEdgeKernelImageEquality",
        "pairIncidenceFoldEqualsPDEGramProvedHereIsFalse",
    ),
    "DASHI/Foundations/TernaryGolay/MathieuSourceAtlas.agda": (
        "10.4153/CMB-1969-005-8",
        "10.1080/10586458.2006.10128958",
        "A Presentation of the Mathieu Group M12",
    ),
    "DASHI/Foundations/TernaryGolay/CompleteWeightEnumerator.agda": (
        "coefficient633",
        "countComposition c633 Explicit.allCodewords ≡ 220",
        "completeCoefficientSum",
    ),
    "DASHI/Foundations/TernaryGolay/PuncturedPerfectCode.agda": (
        "puncturedWeight5",
        "radiusTwoErrorPatternCountIs243",
        "derivedSteinerS4511",
    ),
    "DASHI/Foundations/TernaryGolay/SelfDualityFiniteBoundary.agda": (
        "selfDualFromHalfDimension",
        "allCodewordsOrthogonalToGenerators",
        "concreteRowSpanDualBridgeInCurrentVectorAPIIsFalse",
    ),
    "DASHI/Foundations/TernaryGolay/GolaySelfDualSubspace.agda": (
        "spanEncodeCheckIsTrue",
        "dualCandidateCodeCheckIsTrue",
        "codeToDual",
        "dualToCode",
        "golaySelfDual",
    ),
    "DASHI/Foundations/TernaryGolay/MathieuPresentationAction.agda": (
        "hexadOrbitCountIs132",
        "liftTSquareIsCentralNegation",
        "monomialGroupOrderIs190080",
        "groupIsomorphismKernelCheckedInAgdaIsFalse",
    ),
    "DASHI/Foundations/TernaryGolay/MathieuStabilizerChain.agda": (
        "orderedTwoPointStabilizerOrder = 720",
        "psl211Order = 660",
        "psl211IsOrderedTwoPointStabilizerIsFalse",
    ),
    "DASHI/Foundations/UBP/ObserverConstantProvenance.agda": (
        "craig-v5-4-1-source",
        "observerVersionDeltaExact",
        "silentUpstreamReplacementPermittedIsFalse",
    ),
    "DASHI/Foundations/UBP/ExactRealBackendBoundary.agda": (
        "10.48550/arXiv.2205.08354",
        "10.48550/arXiv.2604.24782",
        "finiteExceptionalLayerDependsOnBishopIsFalse",
    ),
    "DASHI/Foundations/UBP/BishopAbsMigrationReceipt.agda": (
        "d732b0340d729b264227a70fcf38383d8fb3ac3c",
        "K-abs",
        "seq-abs-mul-index",
        "commonIndexTransportRequiredHereIsFalse",
        "10.48550/arXiv.2205.08354",
    ),
    "DASHI/Foundations/UBP/RationalCertificateTransport.agda": (
        "antitoneIntervalTransport",
        "observerCrossDifferenceIdentity",
        "canonicalPiLower",
        "canonicalYLowerCandidate",
        "constructivePiContainmentInstantiatedIsFalse",
    ),
    "DASHI/Foundations/UBP/TaxFiniteDynamicsBoundary.agda": (
        "10.3934/dcdsb.2020331",
        "StronglyConnectedComponent",
        "concreteLeechGraphInstantiatedIsFalse",
    ),
    "DASHI/Analysis/CubicalHoTTRealBackendBoundary.agda": (
        "rationalizable",
        "d732b0340d729b264227a70fcf38383d8fb3ac3c",
        "comparative prototype lane",
    ),
    "scripts/check_explicit_ternary_golay.py": (
        "assert len(permutation_elements) == 95040",
        "assert len(monomial_elements) == 190080",
        "assert len(covered_words) == 3**11",
        "assert 720 != 660",
    ),
    "scripts/check_finite_subspace_self_duality.py": (
        "for word in product(range(3), repeat=12)",
        "assert dual == code",
        "assert sum_zero == anti_diagonal",
        "observer_factor_difference",
    ),
}

FORBIDDEN_AGDA = (
    "{!!}",
    "?}",
    "postulate",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
    "{-# NO_POSITIVITY_CHECK #-}",
    "{-# NO_UNIVERSE_CHECK #-}",
)


def main() -> None:
    failures: list[str] = []

    for relative in REQUIRED_FILES:
        path = ROOT / relative
        if not path.is_file():
            failures.append(f"missing required file: {relative}")

    for relative, needles in REQUIRED_TEXT.items():
        path = ROOT / relative
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        for needle in needles:
            if needle not in text:
                failures.append(f"{relative}: missing required text {needle!r}")

    for relative in REQUIRED_FILES:
        if not relative.endswith(".agda"):
            continue
        path = ROOT / relative
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        for forbidden in FORBIDDEN_AGDA:
            if forbidden in text:
                failures.append(f"{relative}: forbidden escape {forbidden!r}")

    if failures:
        raise SystemExit(
            "Exceptional Mathieu/real-backend audit failed:\n- "
            + "\n- ".join(failures)
        )

    print("Exceptional Mathieu/real-backend static audit passed.")


if __name__ == "__main__":
    main()
