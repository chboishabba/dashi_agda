#!/usr/bin/env python3
"""Fail-closed audit for the periodic finite-Fourier Hodge foundation.

This script checks source shape only. It does not claim to replace Agda typechecking
or to discharge the conditional local-block symbol estimate.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "DASHI" / "Physics" / "YangMills"

REQUIRED = {
    "BalabanPeriodicTorus4Carrier.agda": [
        "periodicTorus4Definition", "periodicTorus4Finite",
        "periodicTorus4DecidableEquality", "dualPeriodicTorus4Definition",
        "momentumCharactersEnumerated", "bondFieldAsAxisIndexedSiteField",
    ],
    "BalabanPeriodicTorus4Fourier.agda": [
        "momentumCharacterDefinition", "momentumCharacterMultiplication",
        "momentumCharacterConjugation", "characterOrthogonality",
        "characterCompleteness", "finiteFourierTransformDefinition",
        "finiteInverseFourierTransformDefinition", "finiteFourierInversionLeft",
        "finiteFourierInversionRight", "bondFourierInversion",
        "fourierParsevalForBondFields", "latticeSpacingNormalizationParseval",
    ],
    "BalabanPeriodicDifferenceSymbols.agda": [
        "forwardDifferenceFourierSymbol", "backwardDifferenceFourierSymbol",
        "latticeGradientFourierSymbol", "latticeDivergenceFourierSymbol",
        "latticeCurlFourierSymbol", "latticeCodifferentialFourierSymbol",
        "gaugeFixingOperatorFourierSymbol", "blockConstraintOperatorFourierSymbol",
        "referenceHessianFourierSymbol", "referenceSymbolFormula",
        "finiteFourierDiagonalizesReferenceLaplacian",
    ],
    "BalabanPeriodicBlockSymbolGap.agda": [
        "forwardDifferenceSymbolNormSq", "referenceSymbolSumOfSquares",
        "referenceSymbolNonnegative", "referenceSymbolKernelIffConstantMode",
        "combinedConstraintsRemoveSymbolKernel",
        "globalMeanZeroDoesNotGiveVolumeUniformGap",
        "localBlockZeroGivesBlockScaleGap", "constrainedSymbolPointwiseLowerBound",
        "constrainedSymbolGapIndependentOfVolume",
        "constrainedSymbolGapIndependentOfSpacing",
        "constrainedSymbolGapIndependentOfRGScale",
        "constrainedSymbolGapUniformInAdmissibleBackground",
        "constrainedReferenceSymbolHasPositiveGap", "cBulkPositive",
        "localBlockGapInputLevel = conditional",
    ],
    "BalabanPeriodicFiniteFourierHodgeCertificate.agda": [
        "periodicFiniteFourierHodgeData",
        "periodicBulkGaugeFixedHodgePoincare",
        "periodicUniformBulkHodgeCertificate",
        "periodicPhysicalLocalBlockGapLevel = conditional",
    ],
    "BalabanPeriodicFourierHodgeRegression.agda": [
        "siteEnumerationRegression", "bondInversionRegression",
        "bondParsevalRegression", "periodicHodgeRegression",
    ],
}

FORBIDDEN = ("postulate", "{!!}", "{-# TERMINATING #-}")

errors: list[str] = []
for filename, needles in REQUIRED.items():
    path = BASE / filename
    if not path.exists():
        errors.append(f"missing {path.relative_to(ROOT)}")
        continue
    text = path.read_text(encoding="utf-8")
    for forbidden in FORBIDDEN:
        if forbidden in text:
            errors.append(f"{filename}: forbidden proof escape {forbidden!r}")
    for needle in needles:
        if needle not in text:
            errors.append(f"{filename}: missing required surface {needle!r}")

if errors:
    print("[fail] periodic finite-Fourier foundation audit")
    for error in errors:
        print(f" - {error}")
    raise SystemExit(1)

print("[ok] periodic finite-Fourier foundation is present and fail-closed")
print("[note] the physical local-block gap remains explicitly conditional")
