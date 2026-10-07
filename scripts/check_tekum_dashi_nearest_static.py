#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/ComputerScience/TekumExactNearestRoundingSemantics.agda": [
        "FiniteTekumWord", "finiteWordValue", "tekumDistance", "Nearest", "NearestSet"
    ],
    "DASHI/ComputerScience/TekumNearestRoundingEnumerationExact.agda": [
        "ordinaryFiniteTargets", "exactNearestSet", "nearestSetNonempty", "nearestDistanceMinimal"
    ],
    "DASHI/ComputerScience/TekumCanonicalNearestTieExact.agda": [
        "CanonicalTieKey", "canonicalNearest", "canonicalNearestInExactNearestSet", "dashiNearestRound"
    ],
    "DASHI/ComputerScience/TekumRawNearestCorrectionExact.agda": [
        "rawTruncationCandidate", "rawTargetOrdinary", "rawNearestDisplacement"
    ],
    "DASHI/ComputerScience/TekumEfficientNearestRoundingExact.agda": [
        "uniformLocalCorrectionNotEstablished"
    ],
    "DASHI/ComputerScience/TekumNearestNoDoubleRoundingExact.agda": [
        "dashiNearestNoDoubleRoundingCounterexample", "universalNoDoubleRoundingRefuted"
    ],
    "DASHI/ComputerScience/TekumDASHIRoundingBoundaryExact.agda": [
        "hunholdRawTruncationNearestRefuted", "dashiExactNearestSemanticsPresent",
        "nearestExistencePaid", "canonicalTieRulePaid", "rawCorrectionRadiusCharacterized",
        "efficientNearestImplementationPaid", "efficientNearestEqualsSemanticOraclePaid",
        "nearestNoDoubleRoundingPaid", "nearestNoDoubleRoundingRefuted"
    ],
}

for rel, needles in REQUIRED.items():
    path = ROOT / rel
    assert path.exists(), f"missing {rel}"
    text = path.read_text()
    for needle in needles:
        assert needle in text, f"missing {needle} in {rel}"

sem = (ROOT / "DASHI/ComputerScience/TekumExactNearestRoundingSemantics.agda").read_text()
assert "Sem.special Sem.naR" not in sem or "FiniteTekumWord" in sem
assert "ordinaryRational" in sem

assembly = (ROOT / "DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda").read_text()
assert "sourceProp5NearestRoundingPaid : Bool" in assembly
assert "numericalNoDoubleRoundingPaid : Bool" in assembly
print("DASHI exact-nearest static surface: OK")
