#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

required = {
    ROOT / "DASHI/Moonshine/OggSSP2BAugmentationArrowEliminationExact.agda": [
        "zeroRelevantArrowsForceTrivialNormalAction",
        "nontrivialActionProducesRelevantArrow",
    ],
    ROOT / "DASHI/Moonshine/OggSSP2BCentralizerMod2CancellationRigidityExact.agda": [
        "runtimeDecompositionIsPaid",
        "actualTateJHProfileIsPaid",
        "commonSupportSeparationIsPaid",
        "residual24UniqueSimpleIsPaid",
        "residualBlockProjectorSameObjectStillOpen",
        "common98280NoLongerIndependentGate",
    ],
    ROOT / "DASHI/Moonshine/OggSSP2BCo1FrobeniusHomRigidityExact.agda": [
        "homUniquenessRuntimeIsPaid",
        "residual24LaneIsRigid",
        "inducedActualResidualEquivarianceStillOpen",
        "common98280MapNoLongerIndependentGate",
    ],
    ROOT / "DASHI/Moonshine/OggSSP2BNormWeldCompilerExact.agda": [
        "residualRankForcedTwentyFour",
        "commonKernelForced98280",
        "ResidualBlockNormSameObjectReceipt",
        "ResidualBlockNormWeldCompiler",
        "tateCokernelForcedExteriorSquareFromResidualBlock",
        "onlyResidualBlockMapRemains",
    ],
}

missing = []
for path, needles in required.items():
    if not path.exists():
        missing.append(f"missing file: {path.relative_to(ROOT)}")
        continue
    text = path.read_text()
    for needle in needles:
        if needle not in text:
            missing.append(f"{path.relative_to(ROOT)} missing marker {needle}")

# Arithmetic max-cut: residual support <=24 plus injective paired norm into a
# 98280-dimensional common lane has no slack.
solutions = [
    (rank, 98304 - rank)
    for rank in range(25)
    if 98304 - rank <= 98280
]
assert solutions == [(24, 98280)]
assert 98580 - 98304 == 276
assert 98304 - 98280 == 24
assert 300 - 24 == 276

# Firewalls: current Agda frontier must not pretend the final same-object weld
# or residual block projector is already paid.
rigidity = (ROOT / "DASHI/Moonshine/OggSSP2BCentralizerMod2CancellationRigidityExact.agda").read_text()
assert "residualBlockProjectorSameObjectPaid\n    canonicalCancellationRigidityBoundary\n  ≡ false" in rigidity
hom = (ROOT / "DASHI/Moonshine/OggSSP2BCo1FrobeniusHomRigidityExact.agda").read_text()
assert "inducedActualResidualEquivariancePaid\n    canonicalFrobeniusHomRigidityBoundary\n  ≡ false" in hom

if missing:
    raise SystemExit("\n".join(missing))

print("2B norm-weld max-cut regression: PASS")
print("forced residual/common ranks:", solutions[0])
print("remaining same-object gate: residual block projector/equivariance + induced Co1 equivariance")
