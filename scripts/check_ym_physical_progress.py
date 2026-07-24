#!/usr/bin/env python3
"""Fail-closed audit for the physical fibre, coercivity, SU(2), polymer and RG tranche."""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanFiniteEnumerationDistinctExact.agda": (
        "allCyclicIndicesDuplicateFree",
        "mapDuplicateFree",
        "cartesianDuplicateFree",
        "cartesianEnumerationDuplicateFreeLevel = machineChecked",
    ),
    YM / "BalabanPhysicalBlockEnumerationDistinctExact.agda": (
        "physicalBlockSitesDuplicateFree",
        "physicalAxisFibreDuplicateFree",
        "physicalFibreEnumerationDuplicateFree",
        "physicalPositiveEdgesDuplicateFree",
        "physicalPositiveEdgesDuplicateFreeLevel = machineChecked",
    ),
    YM / "BalabanPath4AxisAverageNormContractionExact.agda": (
        "axisAveragePythagoras",
        "axisAverageNormContraction",
        "path4AxisAveragePythagorasLevel = machineChecked",
        "path4AxisAverageNormContractionLevel = machineChecked",
    ),
    YM / "BalabanPath4DirectionalEnergyContractionExact.agda": (
        "axisAverageCommutesWithDistinctEdgeDifference",
        "globalEdgeDifferenceNormFourfold",
        "fourTimesDirectionalEnergyContraction",
        "distinctAxisDirectionalEnergyContraction",
        "path4DistinctAxisDirectionalEnergyContractionLevel = machineChecked",
    ),
    YM / "BalabanPath4GlobalPoincareExact.agda": (
        "axisCenteringDirectionalEnergyExact",
        "path4MartingaleDirectionalEnergyContraction",
        "path4GlobalPoincare",
        "path4GlobalPoincareLevel = machineChecked",
    ),
    YM / "BalabanPath4BondHodgeCoercivityExact.agda": (
        "bondReferenceDifferenceEnergy",
        "path4BondDifferencePoincare",
        "path4BondReferenceHodgeCoercivity",
        "path4BondReferenceHodgeCoercivityLevel = machineChecked",
        "literalGaugeBlockPenaltyIdentificationLevel = conditional",
    ),
    YM / "BalabanPath4SU2PhysicalTangentExact.agda": (
        "physicalPositiveBondEnumeration4",
        "physicalPositiveBondEnumeration4Complete",
        "physicalPositiveBondEnumeration4DuplicateFree",
        "physicalTangentComponent",
        "physicalTangentNormMatchesBondNorm",
        "physicalTangentNormComponentExpansionExact",
        "physicalBlockConstraintRemovesComponentMeans",
        "physicalBlockConstrainedDifferencePoincare",
        "path4SU2PhysicalTangentCarrierLevel = machineChecked",
        "physicalPositiveBondEnumeration4DuplicateFreeLevel = machineChecked",
        "physicalTangentNormMatchesBondNormLevel = machineChecked",
        "physicalBlockConstraintRemovesComponentMeansLevel = machineChecked",
    ),
    YM / "BalabanSU2GaugeFixedHessianQuadraticExact.agda": (
        "physicalGaugeFixingQuadraticFormExact",
        "physicalBlockPenaltyQuadraticFormExact",
        "blockConstrainedImpliesPenaltyZero",
        "gaugeFixedHessianQuadraticFormExact",
        "physicalGaugeFixingQuadraticFormExactLevel = machineChecked",
        "physicalBlockPenaltyQuadraticFormExactLevel = machineChecked",
    ),
    YM / "BalabanPath4SU2ReferenceHodgePhysicalExact.agda": (
        "referenceCovariantEnergyMatchesDifferenceEnergy",
        "referenceDifferenceBelowPhysicalHessian",
        "uniformReferenceHodgeCoercivity",
        "path4SU2ReferenceHodgeAssemblyLevel = machineChecked",
        "referenceWilsonDifferenceIdentificationLevel = conditional",
    ),
    YM / "BalabanSU2AdjointPointwiseRadiusSquared.agda": (
        "SU2AdjointSquaredRadiusOrderLaws",
        "unitQuaternionAdjointDisplacementRadiusSqPointwise",
        "SU2ExponentialPointwiseRadiusMatch",
        "exponentialAdjointDisplacementRadiusSqPointwise",
        "su2PointwiseRadiusInterfaceRepairLevel = machineChecked",
        "su2PointwiseExponentialAnalyticInputLevel = conditional",
    ),
    YM / "BalabanSU2RadialExponentialChartExact.agda": (
        "radialQuaternionNormExact",
        "radialImaginaryNormExact",
        "radialDataToPointwiseExponentialMatch",
        "radialExponentialAdjointDisplacementRadiusSq",
        "su2RadialQuaternionAlgebraLevel = computed",
        "su2RadialExponentialChartReductionLevel = machineChecked",
        "su2RadialScalarRadiusBoundLevel = conditional",
    ),
    YM / "BalabanPhysicalHaloOriginExact.agda": (
        "cyclicPredecessor",
        "shiftBackFourfold",
        "physicalOffsetAfterOrigin",
        "physicalOriginAfterOffset",
        "physicalHaloOriginRoundTrips",
        "literalPhysicalContainingOriginCount",
        "physicalBlockOriginOffsetBijectionLevel = machineChecked",
        "physicalOriginMatchesWilsonBlockContainmentLevel = conditional",
    ),
    YM / "BalabanCommutingProjectionMartingaleExact.agda": (
        "residualOrthogonalToFixed",
        "commutingResidualPreservesFixed",
        "martingale01Zero",
        "martingale23Zero",
        "commutingProjectionMartingaleOrthogonalityLevel = machineChecked",
        "physicalAxisAverageSelfAdjointnessLevel = conditional",
    ),
    YM / "BalabanConcreteRootedTracePolymer.agda": (
        "rootedTracePolymerEncoding",
        "tracePolymersOfSizeComplete",
        "tracePolymersOfSizeCount",
        "tracePolymerDiameterBelowAnisotropic",
        "rootedTracePolymerEntropyLevel = machineChecked",
        "physicalConnectedPolymerCanonicalTraceLevel = conditional",
    ),
    YM / "BalabanRunningCouplingIterationExact.agda": (
        "iteratedInverseCouplingFormula",
        "physicalIteratedInverseCouplingFormula",
        "terminalOffsetSpacingExact",
        "transmutationScaleFiniteRGInvariant",
        "runningCouplingFiniteIterationLevel = machineChecked",
        "physicalBetaRemainderEstimateLevel = conditional",
        "physicalTerminalOffsetBoundLevel = conjectural",
    ),
    YM / "BalabanClayAnalyticInhabitationSpine.agda": (
        "physicalFibreScaledMeanZeroLevel = machineChecked",
        "path4PhysicalFibrePoincareLevel = machineChecked",
        "su2AdjointSquaredRadiusConsequenceLevel = machineChecked",
        "finiteTraceKoteckyPreissBoundLevel = machineChecked",
        "runningCouplingFiniteIterationLevel = machineChecked",
        "physicalHessianCoefficientDerivationLevel = conditional",
        "physicalTerminalOffsetBoundLevel = conjectural",
        "clayYangMillsSubmissionPromoted = false",
    ),
    YM / "BalabanPhysicalProgressLedger.agda": (
        "literalPhysicalBlockDistinctnessLevel = machineChecked",
        "path4AxisAverageNormContractionLevel = machineChecked",
        "path4DistinctAxisDirectionalEnergyContractionLevel = machineChecked",
        "path4ScalarGlobalPoincareLevel = machineChecked",
        "path4BondComponentPoincareLevel = machineChecked",
        "path4BondReferenceHodgeCoercivityLevel = machineChecked",
        "path4SU2PhysicalTangentCarrierLevel = machineChecked",
        "physicalPositiveBondEnumeration4DuplicateFreeLevel = machineChecked",
        "physicalTangentNormMatchesBondNormLevel = machineChecked",
        "physicalBlockConstraintRemovesComponentMeansLevel = machineChecked",
        "physicalGaugeFixingQuadraticFormExactLevel = machineChecked",
        "physicalBlockPenaltyQuadraticFormExactLevel = machineChecked",
        "path4SU2ReferenceHodgeAssemblyLevel = machineChecked",
        "referenceWilsonDifferenceIdentificationLevel = conditional",
        "physicalBondHodgeIdentificationLevel = conditional",
        "su2PointwiseRadiusInterfaceRepairLevel = machineChecked",
        "su2RadialExponentialChartReductionLevel = machineChecked",
        "su2RadialScalarRadiusBoundLevel = conditional",
        "literalPhysicalHaloOriginLevel = machineChecked",
        "literalFiveWilsonOperatorBoundsLevel = conditional",
        "physicalTerminalOffsetBoundLevel = conjectural",
    ),
}

SCRIPTS: dict[Path, tuple[str, ...]] = {
    ROOT / "scripts/generate_path_physical_bridge.py": (
        "generate_bridge",
        "physicalFinalCoordinateIsGenerated",
        "physicalNormMatchesGenerated",
        "physicalEnergyMatchesGenerated",
        "physicalFibrePoincare",
    ),
}

FORBIDDEN = (
    "postulate",
    "{!!}",
    "{-# TERMINATING #-}",
    "= _",
)


def fail(message: str) -> None:
    print(f"Physical YM progress audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def audit_text(path: Path, required: tuple[str, ...], forbid: bool) -> None:
    if not path.is_file():
        fail(f"missing {path.relative_to(ROOT)}")
    text = path.read_text(encoding="utf-8")
    if forbid:
        for token in FORBIDDEN:
            if token in text:
                fail(f"forbidden token {token!r} in {path.relative_to(ROOT)}")
    for theorem in required:
        if theorem not in text:
            fail(f"missing {theorem!r} in {path.relative_to(ROOT)}")


def audit_generated_physical_bridge() -> None:
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "GeneratedPath5PhysicalBridge.agda"
        subprocess.run(
            [
                sys.executable,
                str(ROOT / "scripts/generate_path_physical_bridge.py"),
                "5",
                "--certificate-module",
                "DASHI.Physics.YangMills.GeneratedPath5LDLCertificate",
                "--bridge-module",
                "DASHI.Physics.YangMills.GeneratedPath5PhysicalBridge",
                "--output",
                str(output),
            ],
            cwd=ROOT,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        text = output.read_text(encoding="utf-8")
        for theorem in (
            "physicalFinalCoordinateIsGenerated",
            "physicalNormMatchesGenerated",
            "physicalEnergyMatchesGenerated",
            "physicalFibrePoincare",
            "generatedPhysicalFibrePoincareLevel = machineChecked",
        ):
            if theorem not in text:
                fail(f"generated physical bridge missing {theorem!r}")
        for token in FORBIDDEN:
            if token in text:
                fail(f"generated physical bridge contains {token!r}")


def main() -> None:
    for path, required in FILES.items():
        audit_text(path, required, forbid=True)
    for path, required in SCRIPTS.items():
        audit_text(path, required, forbid=False)
    audit_generated_physical_bridge()
    print("Physical fibre, scalar/bond coercivity, SU(2), polymer and RG progress remains exact and fail-closed.")


if __name__ == "__main__":
    main()
