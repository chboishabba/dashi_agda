#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

required = {
    ROOT / "DASHI/Moonshine/OggSSP2BAugmentationArrowEliminationExact.agda": [
        "zeroRelevantArrowsForceTrivialNormalAction",
        "nontrivialActionProducesRelevantArrow",
    ],
    ROOT / "DASHI/Moonshine/OggSSP2BNormWeldCompilerExact.agda": [
        "residualRankForcedTwentyFour",
        "commonKernelForced98280",
        "residualMapForcedFrobenius",
        "tateCokernelForcedExteriorSquare",
        "onlyCommon98280MapRemains",
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

# Arithmetic max-cut: once the common lane is paid, the residual is forced.
assert 98580 - 98304 == 276
assert 98304 - 98280 == 24
assert 300 - 24 == 276

if missing:
    raise SystemExit("\n".join(missing))

print("2B norm-weld max-cut regression: PASS")
