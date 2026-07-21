#!/usr/bin/env python3
"""Fail-closed audit for the dominant-free Balaban background lane."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI" / "Physics" / "YangMills"

EXPECTED = {
    "BalabanReferenceHodgeCoercivity.agda": {
        "referenceHodgeCoercivityAssemblyLevel": "machineChecked",
        "referenceHodgePoincareInputsLevel": "conditional",
    },
    "BalabanPatchRegimeHodgeUniformity.agda": {
        "patchRegimeHodgeAssemblyLevel": "machineChecked",
        "patchRegimeHodgeEstimateInputsLevel": "conditional",
    },
    "BalabanPatchRegimeGreenUniformity.agda": {
        "patchRegimeGreenAssemblyLevel": "machineChecked",
        "patchRegimeGreenEstimateInputsLevel": "conditional",
    },
    "BalabanBackgroundPerturbationBudget.agda": {
        "backgroundPerturbationAssemblyLevel": "machineChecked",
        "backgroundPerturbationComponentInputsLevel": "conditional",
    },
    "BalabanRadiusPerturbationSmallness.agda": {
        "radiusPerturbationAssemblyLevel": "machineChecked",
        "radiusPerturbationCoefficientInputsLevel": "conditional",
    },
    "BalabanCorrectionNeumannBound.agda": {
        "correctionNeumannAssemblyLevel": "machineChecked",
        "strictResidualAndGeometricSumInputsLevel": "conditional",
    },
    "BalabanPatchResidualSmallness.agda": {
        "patchResidualAssemblyLevel": "machineChecked",
        "patchResidualEstimateInputsLevel": "conditional",
    },
    "BalabanSmallFieldNonlinearConstants.agda": {
        "smallFieldNonlinearConstantsAssemblyLevel": "machineChecked",
        "smallFieldCoefficientInputsLevel": "conditional",
    },
    "BalabanExplicitContractionBudget.agda": {
        "explicitContractionBudgetAssemblyLevel": "machineChecked",
        "explicitNumericalSmallnessInputsLevel": "conditional",
    },
    "BalabanExplicitSmallnessWindow.agda": {
        "explicitSmallnessWindowAssemblyLevel": "machineChecked",
        "explicitSmallnessThresholdInputsLevel": "conditional",
    },
    "BalabanCommonSmallFieldRadius.agda": {
        "commonSmallFieldRadiusAssemblyLevel": "machineChecked",
        "commonSmallFieldRadiusExistenceLevel": "conditional",
    },
    "BalabanUniformAnalyticSmallnessClosure.agda": {
        "uniformAnalyticSmallnessAssemblyLevel": "machineChecked",
        "uniformAnalyticSmallnessProducerInputsLevel": "conditional",
    },
    "BalabanAnalyticProducerFrontier.agda": {
        "analyticProducerAssemblyLevel": "machineChecked",
        "analyticProducerEstimateInputsLevel": "conditional",
    },
    "BalabanRelativeHessianCoercivity.agda": {
        "relativeHessianCoercivityBridgeLevel": "machineChecked",
        "referenceCoercivityAndPerturbationInputsLevel": "conditional",
    },
    "BalabanReferenceGreenPerturbation.agda": {
        "referenceGreenPerturbationBridgeLevel": "machineChecked",
        "correctionInverseAndReferenceBoundsLevel": "conditional",
    },
    "BalabanNonlinearComponentLipschitz.agda": {
        "nonlinearComponentAssemblyLevel": "machineChecked",
        "nonlinearComponentEstimateInputsLevel": "conditional",
    },
    "BalabanCriticalBallSelfMap.agda": {
        "criticalBallSelfMapBridgeLevel": "machineChecked",
        "criticalBallAnalyticInputsLevel": "conditional",
    },
    "BalabanDominantFreeBackgroundClosure.agda": {
        "dominantFreeBackgroundAssemblyLevel": "machineChecked",
        "dominantFreeBackgroundProducerInputsLevel": "conditional",
    },
}


def main() -> int:
    failures: list[str] = []
    for name, assignments in EXPECTED.items():
        path = YM / name
        if not path.is_file():
            failures.append(f"missing {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        if re.search(r"(?m)^\s*postulate\b", text):
            failures.append(f"postulate found in {path.relative_to(ROOT)}")
        for declaration, level in assignments.items():
            pattern = rf"(?m)^\s*{re.escape(declaration)}\s*=\s*{level}\s*$"
            if not re.search(pattern, text):
                failures.append(f"missing {declaration} = {level} in {name}")

    if failures:
        print("dominant-free background audit failed", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1

    print(
        "dominant-free background audit passed: "
        f"{len(EXPECTED)} postulate-free modules and "
        f"{sum(len(x) for x in EXPECTED.values())} proof-level assignments"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
