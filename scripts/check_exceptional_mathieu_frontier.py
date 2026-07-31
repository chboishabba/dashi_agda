#!/usr/bin/env python3
"""Static fail-closed audit for the exceptional Mathieu/real-backend frontier."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED_FILES = (
    "DASHI/Foundations/TernaryGolay/MathieuSourceAtlas.agda",
    "DASHI/Foundations/TernaryGolay/CompleteWeightEnumerator.agda",
    "DASHI/Foundations/TernaryGolay/PuncturedPerfectCode.agda",
    "DASHI/Foundations/TernaryGolay/SelfDualityFiniteBoundary.agda",
    "DASHI/Foundations/TernaryGolay/MathieuPresentationAction.agda",
    "DASHI/Foundations/TernaryGolay/MathieuStabilizerChain.agda",
    "DASHI/Foundations/TernaryGolay/FrontierRegression.agda",
    "DASHI/Foundations/UBP/ExactRealSourceAtlas.agda",
    "DASHI/Foundations/UBP/ObserverConstantProvenance.agda",
    "DASHI/Foundations/UBP/ExactRealBackendBoundary.agda",
    "DASHI/Foundations/UBP/TaxFiniteDynamicsBoundary.agda",
    "DASHI/Foundations/UBP/FrontierRegression.agda",
    "Docs/support/reference/ExceptionalMathieuAndRealBackendFrontier.md",
    "scripts/check_explicit_ternary_golay.py",
)

REQUIRED_TEXT = {
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
    "DASHI/Foundations/UBP/TaxFiniteDynamicsBoundary.agda": (
        "10.3934/dcdsb.2020331",
        "StronglyConnectedComponent",
        "concreteLeechGraphInstantiatedIsFalse",
    ),
    "scripts/check_explicit_ternary_golay.py": (
        "assert len(permutation_elements) == 95040",
        "assert len(monomial_elements) == 190080",
        "assert len(covered_words) == 3**11",
        "assert 720 != 660",
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
