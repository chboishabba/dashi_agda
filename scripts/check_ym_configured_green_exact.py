#!/usr/bin/env python3
"""Fail-closed textual audit for the constructive side-four Green closure.

This is not a substitute for Agda kernel validation. It ensures the explicit
translation, convolution, inverse-product and norm-certificate terms remain
wired without postulates, holes or unsafe proof bodies.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanPath4GlobalAverageExact.agda": (
        "average0123EqualsGlobalMean",
        "fourAxisAverageGlobalMeanLevel = machineChecked",
    ),
    YM / "BalabanSide4ScalarGreenKernelComputed.agda": (
        "scalarGreenKernelEquation",
        "scalarGreenKernelTotalExact",
        "scalarGreenKernelComputedLevel = machineChecked",
    ),
    YM / "BalabanSide4TranslationDifferenceExact.agda": (
        "subtractSiteForward",
        "subtractSiteBackward",
        "scalarDeltaAtZeroSubtract",
        "siteSumSubtractInvariant",
    ),
    YM / "BalabanSide4TranslationConvolutionExact.agda": (
        "subtractSiteRightForward",
        "subtractSiteRightBackward",
    ),
    YM / "BalabanSide4TranslationSymmetryExact.agda": (
        "subtractSiteSwapNegate",
    ),
    YM / "BalabanPath4SU2ConfiguredScalarReductionExact.agda": (
        "scalarWilsonGaugeCollapse",
        "configuredGaugeFixedMatrixEqualsLaplacianPlusMean",
    ),
    YM / "BalabanSide4ScalarGreenConvolutionExact.agda": (
        "translatedKernelEquation",
        "configuredSiteGreenRightInverse",
        "configuredSiteGreenLeftInverse",
        "side4ScalarGreenLeftInverseLevel = machineChecked",
    ),
    YM / "BalabanFiniteRationalCauchyExact.agda": (
        "pairDifferenceIdentity",
        "finiteRationalCauchy",
        "finiteRationalCauchyLevel = machineChecked",
    ),
    YM / "BalabanSide4ScalarGreenNormExact.agda": (
        "kernelSquareSumExact",
        "kernelSquareSumBelowOneSixteenth",
        "scalarGreenNormBound",
        "side4ScalarGreenNormLevel = machineChecked",
    ),
    YM / "BalabanPath4SU2ConfiguredGreenExact.agda": (
        "configuredPhysicalGreenLeftInverse",
        "configuredPhysicalGreenRightInverse",
        "configuredGaugeFixedMatrixInverseCertificate",
        "configuredGreenMatrixInverseProductLevel = machineChecked",
    ),
    YM / "BalabanPath4SU2ConfiguredGreenNormExact.agda": (
        "configuredPhysicalGreenNormBound",
        "configuredPhysicalGreenNormLevel = machineChecked",
    ),
    YM / "BalabanClayFrontierCompletionLedger.agda": (
        "constructiveConfiguredFiniteInverseLevel = machineChecked",
        "branchHeadAuthoritativeAgda29TypecheckLevel = conditional",
    ),
}

FORBIDDEN = (
    (re.compile(r"(?m)^\s*postulate\b"), "postulate declaration"),
    (re.compile(r"\{\!\!\}"), "Agda hole"),
    (re.compile(r"\{-#\s*(?:NON_)?TERMINATING\s*#-\}"), "unsafe termination pragma"),
    (re.compile(r"=\s*_\s*(?:\n|$)"), "underscore proof body"),
)


def fail(message: str) -> None:
    print(f"Configured Green audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, tokens in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for pattern, label in FORBIDDEN:
            if pattern.search(text):
                fail(f"forbidden {label} in {path.relative_to(ROOT)}")
        for token in tokens:
            if token not in text:
                fail(f"missing {token!r} in {path.relative_to(ROOT)}")

    print(
        "Exact global averaging, translation, Fourier Green kernel, scalar and "
        "physical two-sided inverse products, and the explicit factor-16 norm "
        "certificate are present and hole-free."
    )


if __name__ == "__main__":
    main()
