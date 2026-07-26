#!/usr/bin/env python3
"""Fail-closed textual audit for the side-four C1 cleanup and C2 exact spine.

This does not replace Agda kernel validation.  It prevents the finite averaging,
coarse/fine, constrained-propagator, translated, background-assembly, and
all-scale induction surfaces from silently losing declarations or gaining holes.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanFiniteSumFubiniExact.agda": (
        "sumRationalAdd",
        "sumRationalAppend",
        "sumSwap",
        "finiteSumAppendLevel = machineChecked",
    ),
    YM / "BalabanPath4AxisAverageExact.agda": (
        "axisAverage4Idempotent",
        "axisAverage4Commutes",
        "axisCentering4DirectFibreSumZero",
        "axisCentering4FibreSumZero",
        "path4AxisAverageIdempotenceLevel = machineChecked",
        "path4DistinctAxisAverageCommutationLevel = machineChecked",
        "path4AxisCenteringMeanZeroLevel = machineChecked",
    ),
    YM / "BalabanPath4SU2ConcreteCoarseBlockExact.agda": (
        "CoarseSU2Bond4",
        "literalBlockAverageQ",
        "literalBlockAverageAdjointQStar",
        "blockAverageAdjointExact",
        "blockAverageCoisometry",
        "blockAverageProjectionIdempotent",
        "blockAverageKernelOrthogonal",
        "concreteLiteralCoarseBlockData",
        "fineFluctuationCoercivity",
    ),
    YM / "BalabanPath4SU2CoarseFineSplittingExact.agda": (
        "fineProjectionReconstruction",
        "coarseFineNormSqExact",
        "coarsePenaltyNormMatchesProjection",
        "coarsePenalizedCoercivity",
    ),
    YM / "BalabanPath4SU2ConcretePropagatorExact.agda": (
        "configuredGaugeFixedMatrix",
        "configuredGaugeFixedMatrixPositive",
        "configuredGaugeFixedMatrixInvertible",
        "configuredPropagator",
        "configuredPropagatorLeftInverse",
        "configuredPropagatorRightInverse",
        "configuredPropagatorNormBound",
        "configuredFiniteCoerciveInverseAuthorityLevel = standardImported",
    ),
    YM / "BalabanPath4SU2TranslatedCoarsePropagatorExact.agda": (
        "translatedBlockAverageCommutes",
        "translatedBlockAdjointCommutes",
        "translatedGaugeFixedOperatorCommutes",
        "translatedPropagatorCommutes",
    ),
    YM / "BalabanPath4SU2BackgroundStabilityExact.agda": (
        "backgroundHessianDifferenceExact",
        "backgroundHessianDifferenceBound",
        "smallBackgroundPreservesCoercivity",
        "backgroundPropagatorNeumannExpansion",
        "backgroundPropagatorNormBound",
        "backgroundPerturbationProducerLevel = conditional",
    ),
    YM / "BalabanC2SmallLargeAllScaleExact.agda": (
        "SmallFieldConfiguration",
        "LargeFieldPolymer",
        "smallFieldHessianUniformCoercivity",
        "largeFieldActionPenalty",
        "polymerActivitySuppression",
        "oneStepRGCoercivityTransfer",
        "allScaleCoercivity",
        "oneStepPolymerRGContraction",
    ),
}

FORBIDDEN_PATTERNS = (
    (re.compile(r"(?m)^\s*postulate\b"), "postulate declaration"),
    (re.compile(r"\{\!\!\}"), "Agda hole"),
    (re.compile(r"\{-#\s*(?:NON_)?TERMINATING\s*#-\}"), "unsafe termination pragma"),
    (re.compile(r"=\s*_\s*(?:\n|$)"), "underscore proof body"),
)


def fail(message: str) -> None:
    print(f"C2 exact-cutset audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, required in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for pattern, label in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                fail(f"forbidden {label} in {path.relative_to(ROOT)}")
        for token in required:
            if token not in text:
                fail(f"missing {token!r} in {path.relative_to(ROOT)}")

    aggregate = YM / "ConstructiveYangMillsNextSurface.agda"
    aggregate_text = aggregate.read_text(encoding="utf-8")
    for module in (
        "BalabanPath4SU2ConcreteCoarseBlockExact",
        "BalabanPath4SU2CoarseFineSplittingExact",
        "BalabanPath4SU2ConcretePropagatorExact",
        "BalabanPath4SU2TranslatedCoarsePropagatorExact",
        "BalabanPath4SU2BackgroundStabilityExact",
        "BalabanC2SmallLargeAllScaleExact",
    ):
        if module not in aggregate_text:
            fail(f"aggregate does not import {module}")

    print(
        "Side-four average laws, concrete Q/Q*, coarse-fine Pythagoras, "
        "constrained propagator assembly, translation compatibility, background "
        "stability assembly, and all-scale coercivity induction are present and "
        "hole-free."
    )


if __name__ == "__main__":
    main()
