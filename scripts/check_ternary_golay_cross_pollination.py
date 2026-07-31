#!/usr/bin/env python3
"""Static fail-closed audit for the ternary-Golay cross-pollination tranche."""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

REQUIRED_FILES = [
    "DASHI/Foundations/UBP/ExternalRepositoryProvenance.agda",
    "DASHI/Foundations/UBP/YIntervalCertificate.agda",
    "DASHI/Foundations/UBP/LeechValidMoveSet.agda",
    "DASHI/Foundations/TernaryGolay/SourceAtlas.agda",
    "DASHI/Foundations/TernaryGolay/ChannelC3OrbitDecomposition.agda",
    "DASHI/Foundations/TernaryGolay/NonaryTernaryReduction.agda",
    "DASHI/Foundations/TernaryGolay/CodeBoundary.agda",
    "DASHI/Foundations/TernaryGolay/RetractedZ9CoxeterToddBoundary.agda",
    "DASHI/Foundations/TernaryGolay/CoxeterToddRoutesBoundary.agda",
    "DASHI/Foundations/TernaryGolay/TGICWalshS3Decomposition.agda",
    "DASHI/Foundations/TernaryGolay/MathieuExceptionalBridgeBoundary.agda",
    "DASHI/Foundations/TernaryGolay/Regression.agda",
]

REQUIRED_TEXT = {
    "DASHI/Foundations/UBP/ExternalRepositoryProvenance.agda": [
        "Euan R. A. Craig (DigitalEuan)",
        "https://github.com/DigitalEuan/UBP_Repo",
        "core_studio_v4.0/core/tgic_v3.py",
        "dashiClaimsOriginalUBPAuthorshipIsFalse",
    ],
    "DASHI/Foundations/TernaryGolay/SourceAtlas.agda": [
        "10.1109/18.485733",
        "10.1109/TIT.2002.806139",
        "10.1017/S0305004100060746",
        "10.1007/978-1-4757-6568-7",
    ],
    "DASHI/Foundations/TernaryGolay/RetractedZ9CoxeterToddBoundary.agda": [
        "constructionProducesK12IsFalse",
        "determinantIsThreePowerTwelve",
        "NoBlock9LiftCanProduceK12",
    ],
    "DASHI/Foundations/TernaryGolay/CoxeterToddRoutesBoundary.agda": [
        "OrderThreeFixedSublatticeRoute",
        "EisensteinRepetitionConstructionRoute",
        "ternaryGolayZ9ConstructionAProducesK12IsFalse",
    ],
    "DASHI/Foundations/TernaryGolay/ChannelC3OrbitDecomposition.agda": [
        "c3OrbitRotationInvariant",
        "swapExchangesCyclicOrientation",
        "swapReturnsToSingleS3Orbit",
        "channelCountIsNine",
    ],
    "DASHI/Foundations/TernaryGolay/NonaryTernaryReduction.agda": [
        "reducePreservesAdd",
        "reducePreservesMul",
        "canonicalNonaryTernaryRingReduction",
    ],
    "DASHI/Foundations/TernaryGolay/TGICWalshS3Decomposition.agda": [
        "symmetrisedPairwiseCoefficient",
        "xyPairwiseBias",
        "pairwiseBiasConstantsSumToZero",
        "DigitalEuan/UBP_Repo",
    ],
}

FORBIDDEN = [
    re.compile(r"\bpostulate\b"),
    re.compile(r"\{!.*?!\}", re.DOTALL),
    re.compile(r"TERMINATING"),
    re.compile(r"NO_POSITIVITY_CHECK"),
    re.compile(r"Z9.*produces.*K12", re.IGNORECASE),
]


def strip_agda_comments(text: str) -> str:
    text = re.sub(r"\{-.*?-\}", "", text, flags=re.DOTALL)
    return re.sub(r"--.*$", "", text, flags=re.MULTILINE)


def main() -> int:
    failures: list[str] = []
    for relative in REQUIRED_FILES:
        path = ROOT / relative
        if not path.is_file():
            failures.append(f"missing required file: {relative}")
            continue
        raw = path.read_text(encoding="utf-8")
        stripped = strip_agda_comments(raw)
        for pattern in FORBIDDEN:
            if pattern.search(stripped):
                failures.append(f"forbidden pattern {pattern.pattern!r}: {relative}")
        for required in REQUIRED_TEXT.get(relative, []):
            if required not in raw:
                failures.append(f"missing required text {required!r}: {relative}")

    if failures:
        print("Ternary-Golay cross-pollination audit failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print("Ternary-Golay cross-pollination audit passed.")
    print(f"Checked {len(REQUIRED_FILES)} required files.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
