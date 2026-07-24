#!/usr/bin/env python3
"""Fail-closed source audit for the periodic physical Hodge/Green closure.

This checks theorem ownership and proof-status separation. It does not replace
Agda typechecking or prove the conditional local-block and perturbation estimates.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "DASHI" / "Physics" / "YangMills"

REQUIRED = {
    "BalabanPeriodicFourierNormalizationMatching.agda": [
        "PeriodicFourierNormalizationMatch",
        "physicalBondFourierParseval",
        "literalTransformUsesInverseCardinality",
        "literalCharacterSumUsesTorusCardinality",
        "periodicFourierNormalizationMatchingLevel = machineChecked",
        "periodicLiteralFiniteFourierTheoremLevel = standardImported",
    ],
    "BalabanPeriodicPhysicalConstraintMatching.agda": [
        "PhysicalConstraintFourierInputs",
        "physicalConstraintRemovalData",
        "physicalGaugeFixedTangentRemovesReferenceKernel",
        "periodicPhysicalConstraintAdapterLevel = machineChecked",
        "periodicPhysicalConstraintFourierInputLevel = conditional",
    ],
    "BalabanPeriodicLocalBlockGapInhabitation.agda": [
        "PhysicalLocalBlockGapInputs",
        "nonzeroMomentumDifferenceSymbolLowerBound",
        "lowMomentumControlledByLocalBlockConstraint",
        "physicalLocalBlockGapImpliesUniformReferenceGap",
        "physicalCBulkIndependentOfVolume",
        "physicalCBulkIndependentOfSpacing",
        "physicalCBulkIndependentOfRGScale",
        "physicalCBulkUniformInBackground",
        "periodicLocalBlockGapAssemblyLevel = machineChecked",
        "periodicHighFrequencyTrigonometricInputLevel = standardImported",
        "periodicLowFrequencyLocalBlockPoincareInputLevel = conditional",
    ],
    "BalabanPeriodicBulkHessianGreenClosure.agda": [
        "PeriodicBulkHessianGreenInputs",
        "fiveComponentHessianPerturbationBound",
        "periodicReferenceHessianCoercive",
        "uniformConstrainedHessianCoercive",
        "PeriodicBulkHessianGreenCertificate",
        "periodicFivePerturbationAssemblyLevel = machineChecked",
        "periodicFullHessianCoercivityAssemblyLevel = machineChecked",
        "periodicFivePerturbationInputLevel = conditional",
        "periodicFiniteCoerciveInverseInputLevel = standardImported",
        "periodicBulkGreenKernelInputLevel = standardImported",
    ],
    "BalabanPeriodicPhysicalClosureRegression.agda": [
        "physicalParsevalRegression",
        "physicalKernelRemovalRegression",
        "localGapRegression",
        "fullHessianCoercivityRegression",
        "bulkGreenCertificate",
    ],
    "BalabanPeriodicPatchGreenTransfer.agda": [
        "PhysicalPatchOperatorTransfer",
        "physicalPatchOperatorBound",
        "PhysicalPatchTripleTransfer",
        "assemblePhysicalPatchTripleBounds",
        "FourPhysicalPatchTransferFamily",
        "periodicPatchTransferAssemblyLevel = machineChecked",
        "periodicConcretePatchGeometryInputLevel = conditional",
    ],
    "BalabanPeriodicPatchGreenTransferRegression.agda": [
        "greenTransfer",
        "gradientTransfer",
        "secondGradientTransfer",
        "boundaryGreenRegression",
        "fourRegimeFamily",
    ],
    "BalabanPeriodicConstructiveCompletionSpine.agda": [
        "PeriodicConstructiveCompletionSpine",
        "patchTransferFamily",
        "residualWitness",
        "oneStepAllScaleInputs",
        "thermodynamicContinuumInputs",
        "physicalMassGapInputs",
        "projectPeriodicConstructiveCompletionEndpoints",
        "periodicConstructiveCompletionSpineAssemblyLevel = machineChecked",
        "periodicPatchResidualInputLevel = conditional",
        "periodicOneStepAllScaleInputLevel = conditional",
        "periodicThermodynamicContinuumInputLevel = conjectural",
        "periodicPhysicalGapInputLevel = conjectural",
    ],
    "BalabanClayAnalyticInhabitationSpine.agda": [
        "periodicFourierNormalizationMatchingLevel = machineChecked",
        "periodicPhysicalConstraintAdapterLevel = machineChecked",
        "periodicPhysicalConstraintFourierInputLevel = conditional",
        "periodicLocalBlockGapAssemblyLevel = machineChecked",
        "periodicLocalBlockGapInputLevel = conditional",
        "periodicFivePerturbationAssemblyLevel = machineChecked",
        "periodicFivePerturbationInputLevel = conditional",
        "periodicFullHessianCoercivityAssemblyLevel = machineChecked",
        "periodicPatchTransferAssemblyLevel = machineChecked",
        "periodicConcretePatchGeometryInputLevel = conditional",
        "periodicConstructiveCompletionSpineAssemblyLevel = machineChecked",
        "periodicPatchResidualInputLevel = conditional",
        "periodicOneStepAllScaleInputLevel = conditional",
        "periodicThermodynamicContinuumInputLevel = conjectural",
        "periodicPhysicalGapInputLevel = conjectural",
        "clayYangMillsSubmissionPromoted = false",
    ],
}

FORBIDDEN = ("postulate", "{!!}", "{-# TERMINATING #-}", "= _")
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
    print("[fail] periodic physical closure audit")
    for error in errors:
        print(f" - {error}")
    raise SystemExit(1)

print("[ok] periodic physical closure is present and fail-closed")
print("[note] physical Fourier identities, local-block Poincare, five perturbation bounds and downstream analytic owners remain explicit inputs")
