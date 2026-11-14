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
        "rawTruncationCandidate", "rawTargetOrdinary", "rawNearestDisplacement",
        "uniformRadiusOneRawCorrectionRefuted"
    ],
    "DASHI/ComputerScience/TekumEfficientNearestRoundingExact.agda": [
        "uniformLocalCorrectionNotEstablished"
    ],
    "DASHI/ComputerScience/TekumNearestNoDoubleRoundingExact.agda": [
        "dashiNearestNoDoubleRoundingCounterexample", "universalNoDoubleRoundingRefuted",
        "sourceDecoderSameObject", "intermediateDecoderSameObject",
        "twoStageDecoderSameObject", "directDecoderSameObject"
    ],
    "DASHI/ComputerScience/TekumDASHIRoundingBoundaryExact.agda": [
        "hunholdRawTruncationNearestRefuted", "dashiExactNearestSemanticsPresent",
        "nearestExistencePaid", "canonicalTieRulePaid", "rawCorrectionRadiusCharacterized",
        "efficientNearestImplementationPaid", "efficientNearestEqualsSemanticOraclePaid",
        "nearestNoDoubleRoundingPaid", "nearestNoDoubleRoundingRefuted",
        "nearestNoDoubleMutualExclusion"
    ],
    "DASHI/ComputerScience/TekumDASHIRoundingAssemblyExact.agda": [
        "TekumBalancedTernaryVerifiedAssembly", "TekumDASHIRoundingBoundaryExact"
    ],
}

for rel, needles in REQUIRED.items():
    path = ROOT / rel
    assert path.exists(), f"missing {rel}"
    text = path.read_text()
    for needle in needles:
        assert needle in text, f"missing {needle} in {rel}"

sem = (ROOT / "DASHI/ComputerScience/TekumExactNearestRoundingSemantics.agda").read_text()
assert "ordinaryRational" in sem
assert "truncateTwo" not in sem, "raw truncation leaked into semantic authority"

assembly = (ROOT / "DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda").read_text()
assert "sourceProp5NearestRoundingPaid : Bool" in assembly
assert "numericalNoDoubleRoundingPaid : Bool" in assembly

boundary = (ROOT / "DASHI/ComputerScience/TekumDASHIRoundingBoundaryExact.agda").read_text()
assert "false  -- general Agda finite-minimum witness construction still separate" in boundary
assert "noDoubleRefuted" in boundary

receipt = (ROOT / "docs/superpowers/receipts/2026-10-07-tekum-nearest-rounding-enumeration.md").read_text()
for needle in ("59,046", "6,558", "531,438", "59,046", "-265591"):
    assert needle in receipt

print("DASHI exact-nearest static surface: OK")
