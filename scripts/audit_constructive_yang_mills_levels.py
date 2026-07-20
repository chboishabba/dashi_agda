#!/usr/bin/env python3
"""Static honesty audit for the constructive Yang--Mills proof-level stack.

This does not prove mathematics. It prevents accidental promotion by checking
that locally checked assembly modules contain no postulates, imported theorem
sockets remain non-promotable, frontier inputs retain conditional/conjectural
levels, and the repository Clay promotion flag is not set to true.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI" / "Physics" / "YangMills"
GAUGE = ROOT / "DASHI" / "Geometry" / "Gauge"

POSTULATE_FREE = [
    YM / "SUNMatrixCarrier.agda",
    YM / "SUNMatrixLieAlgebra.agda",
    YM / "SUNMatrixLieGroup.agda",
    YM / "SUNMatrixGeometry.agda",
    YM / "SU3MatrixInstance.agda",
    YM / "SUNWilsonClassFunction.agda",
    YM / "SUNWilsonAction.agda",
    YM / "BalabanFiniteInverseConsequences.agda",
    YM / "BalabanFiniteVolumeBackgroundLane.agda",
    YM / "BalabanOneStepRGClosure.agda",
    YM / "BalabanStepVKPClosure.agda",
    YM / "BalabanAllScaleRGClosure.agda",
    YM / "BalabanOSMassGapClosure.agda",
    YM / "BalabanDashenGrossCalibration.agda",
]

EXPECTED_ASSIGNMENTS = {
    YM / "SUNMatrixCarrier.agda": {
        "sunMatrixCarrierLevel": "machineChecked",
        "finiteComplexMatrixAuthorityLevel": "standardImported",
    },
    YM / "SUNMatrixLieAlgebra.agda": {
        "sunMatrixLieAlgebraLevel": "machineChecked",
        "finiteMatrixLieIdentityAuthorityLevel": "standardImported",
    },
    YM / "SUNMatrixLieGroup.agda": {
        "sunMatrixLieGroupAssemblyLevel": "machineChecked",
        "sunTopologyAndExponentialAuthorityLevel": "standardImported",
    },
    YM / "SUNMatrixGeometry.agda": {
        "sunMetricAndChartAssemblyLevel": "machineChecked",
        "sunMetricAndChartAuthorityLevel": "standardImported",
    },
    YM / "SU3MatrixInstance.agda": {
        "su3DimensionLevel": "computed",
        "su3MatrixAssemblyLevel": "machineChecked",
        "su3FiniteMatrixAuthorityLevel": "standardImported",
    },
    YM / "SUNWilsonClassFunction.agda": {
        "sunWilsonGaugeInvarianceLevel": "machineChecked",
        "sunTraceConjugationAuthorityLevel": "standardImported",
    },
    YM / "SUNWilsonAction.agda": {
        "sunWilsonActionGaugeInvarianceLevel": "machineChecked",
        "sunWilsonTraceAuthorityLevel": "standardImported",
    },
    YM / "BalabanFiniteVolumeBackgroundLane.agda": {
        "finiteVolumeContractionBridgeLevel": "machineChecked",
        "finiteVolumeGreenAndRemainderInputsLevel": "conditional",
        "finiteVolumeBackgroundConclusionLevel": "conditional",
    },
    YM / "BalabanOneStepRGClosure.agda": {
        "oneStepRGAssemblyLevel": "machineChecked",
        "oneStepRGAnalyticInputsLevel": "conditional",
    },
    YM / "BalabanStepVKPClosure.agda": {
        "stepVKPBridgeLevel": "machineChecked",
        "stepVSpatialInputsLevel": "conjectural",
    },
    YM / "BalabanAllScaleRGClosure.agda": {
        "allScaleInductionLevel": "machineChecked",
        "allScaleOneStepPreservationLevel": "conjectural",
    },
    YM / "BalabanOSMassGapClosure.agda": {
        "osReconstructionLevel": "standardImported",
        "continuumOSAxiomsLevel": "conjectural",
        "clusteringToGapTransferLevel": "standardImported",
        "physicalMassGapInputLevel": "conjectural",
    },
    YM / "BalabanDashenGrossCalibration.agda": {
        "dashenGrossCalibrationAssemblyLevel": "machineChecked",
        "dashenGrossNumericalConstantsLevel": "standardImported",
    },
}


def read(path: Path) -> str:
    if not path.is_file():
        raise FileNotFoundError(path.relative_to(ROOT))
    return path.read_text(encoding="utf-8")


def main() -> int:
    errors: list[str] = []

    for path in POSTULATE_FREE:
        try:
            text = read(path)
        except FileNotFoundError as exc:
            errors.append(f"missing audited file: {exc}")
            continue
        if re.search(r"(?m)^\s*postulate\b", text):
            errors.append(f"postulate found in locally checked module: {path.relative_to(ROOT)}")

    for path, assignments in EXPECTED_ASSIGNMENTS.items():
        try:
            text = read(path)
        except FileNotFoundError:
            continue
        for name, level in assignments.items():
            pattern = rf"(?m)^\s*{re.escape(name)}\s*=\s*{re.escape(level)}\s*$"
            if not re.search(pattern, text):
                errors.append(
                    f"missing proof-level assignment {name} = {level} in {path.relative_to(ROOT)}"
                )

    promotion_file = GAUGE / "SUNPrimitives.agda"
    try:
        promotion_text = read(promotion_file)
        if re.search(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$", promotion_text):
            errors.append("Clay Yang--Mills promotion flag was set to true")
        if not re.search(r"(?m)^\s*clayYangMillsPromoted\s*=\s*false\s*$", promotion_text):
            errors.append("Clay Yang--Mills promotion flag is not explicitly false")
    except FileNotFoundError as exc:
        errors.append(f"missing promotion flag file: {exc}")

    if errors:
        print("constructive Yang--Mills proof-level audit failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(
        "constructive Yang--Mills proof-level audit passed: "
        f"{len(POSTULATE_FREE)} postulate-free modules, "
        f"{sum(map(len, EXPECTED_ASSIGNMENTS.values()))} level assignments, "
        "Clay promotion false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
