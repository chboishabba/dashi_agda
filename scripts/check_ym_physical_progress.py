#!/usr/bin/env python3
"""Fail-closed audit for the physical fibre, polymer and RG progress tranche."""

from __future__ import annotations

from pathlib import Path
import sys

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
        "literalPhysicalHaloOriginLevel = machineChecked",
        "commutingProjectionOrthogonalityLevel = machineChecked",
        "literalFiveWilsonOperatorBoundsLevel = conditional",
        "physicalTerminalOffsetBoundLevel = conjectural",
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


def main() -> None:
    for path, required in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            if token in text:
                fail(f"forbidden token {token!r} in {path.relative_to(ROOT)}")
        for theorem in required:
            if theorem not in text:
                fail(f"missing {theorem!r} in {path.relative_to(ROOT)}")
    print("Physical fibre, polymer and RG progress remains exact and fail-closed.")


if __name__ == "__main__":
    main()
