#!/usr/bin/env python3
"""Audit the official-norm/expenditure/coverage Agda surface."""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

FILES = {
    "NSPeriodicOfficialNormIdentification.agda": [
        "officialShellVorticityL2FromVelocity",
        "officialShellVorticityFromVelocity",
        "officialVorticityReconstruction",
        "officialPeriodicNormIdentificationInhabited = false",
    ],
    "NSPeriodicOfficialNormBernsteinAdapter.agda": [
        "concreteBernsteinToOfficialNormIdentification",
        "shellCurlFromConcreteBernstein",
        "vorticityReconstructionFromConcreteLeaves",
    ],
    "NSPeriodicNearTriadCutoffUniformCompletion.agda": [
        "periodicNearTriadCutoffUniformEstimate",
        "nearTriadOfficialUniformInputsInhabited = false",
    ],
    "NSPeriodicFarLowOfficialSchurCompletion.agda": [
        "periodicFarLowOfficialRadiusEightEstimate",
        "farLowOfficialSchurInputsInhabited = false",
    ],
    "NSPeriodicFarHighTailCompletion.agda": [
        "periodicFarHighOfficialRadiusEightEstimate",
        "farHighOfficialTailInputsInhabited = false",
    ],
    "NSPeriodicOfficialHarmonicAuthorityCompletion.agda": [
        "nearTriadFromSelectedAuthority",
        "farLowFromSelectedAuthority",
        "farHighFromSelectedAuthority",
    ],
    "NSPeriodicWallIHarmonicCompletion.agda": [
        "wallIOfficialNormAdmissibility",
        "periodicWallIHarmonicEstimate",
        "wallIOfficialHarmonicInputsInhabited = false",
    ],
    "NSPeriodicIntegratedExpenditureCompletion.agda": [
        "periodicIntegratedWeightedShellEstimate",
        "periodicIntegratedVorticityEstimate",
        "periodicIntegratedBKMContinuation",
        "periodicConcreteExpenditureInputsInhabited = false",
    ],
    "NSCompactGammaNormalizedBoundaryInwardnessCompletion.agda": [
        "normalizedAdaptiveCoverageNoFirstExit",
        "normalizedBoundaryPDEInputsInhabited = false",
    ],
    "NSPeriodicAdaptiveSwitchCostCompletion.agda": [
        "adaptiveSwitchingIsControlled",
        "adaptiveTotalSwitchCostBound",
        "adaptiveSwitchCostInputsInhabited = false",
    ],
    "NSPeriodicDiffuseSpectrumBKMCompletion.agda": [
        "periodicDiffuseSpectrumGivesBKM",
        "diffuseSpectrumBKMInputsInhabited = false",
    ],
    "NSPeriodicAllDataCoverageCompletion.agda": [
        "periodicAllDataContinuesBeyond",
        "allDataAdaptiveCoverageInputsInhabited = false",
    ],
    "NSPeriodicStandardContinuumAdapter.agda": [
        "standardLimitIsLerayHopf",
        "standardCompactGammaCutoffEstimatePasses",
        "standardContinuumBKMContinuation",
    ],
    "NSPeriodicCutoffUniformContinuumBKMCompletion.agda": [
        "periodicContinuumGlobalRegularity",
        "unconditionalPeriodicGlobalRegularityPromoted = false",
    ],
    "NSPeriodicOfficialCompletionStatus.agda": [
        "unconditionalPeriodicNavierStokesTheorem = false",
        "clayNavierStokesSubmissionPromoted = false",
    ],
    "NSPeriodicOfficialCompletionRegression.agda": [
        "globalRegularityGateRegression = refl",
        "clayGateRegression = refl",
    ],
}

FORBIDDEN = (
    "postulate",
    "{!!}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
    "unconditionalPeriodicNavierStokesTheorem = true",
    "clayNavierStokesSubmissionPromoted = true",
)


def main() -> None:
    errors: list[str] = []
    for name, required in FILES.items():
        path = CLOSURE / name
        if not path.is_file():
            errors.append(f"missing file: {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        for token in required:
            if token not in text:
                errors.append(f"{name}: missing required token {token!r}")
        for token in FORBIDDEN:
            if token in text:
                errors.append(f"{name}: forbidden token {token!r}")

    if errors:
        for error in errors:
            print(f"[error] {error}")
        raise SystemExit(1)

    print(
        "[ok] official periodic norm/expenditure/coverage surface is complete "
        "and fail-closed"
    )


if __name__ == "__main__":
    main()
