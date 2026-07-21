#!/usr/bin/env python3
"""Fail-closed static audit of the concrete periodic proof-program surface."""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "NSPeriodicConcreteCarrier.agda",
    "NSPeriodicConcreteCarrierCoherence.agda",
    "NSPeriodicConcreteDyadicPartition.agda",
    "NSPeriodicConcreteMultiplierScalingReceipt.agda",
    "NSPeriodicConcreteNorms.agda",
    "NSPeriodicConcreteCompactGamma.agda",
    "NSPeriodicConcreteTriadForms.agda",
    "NSPeriodicConcreteNearTriadDecomposition.agda",
    "NSPeriodicConcreteNearTriadScanReceipt.agda",
    "NSPeriodicConcreteRationalCertificate.agda",
    "NSPeriodicConcreteFullOperatorReceipt.agda",
    "NSPeriodicConcreteFiveHalvesFalsification.agda",
    "NSPeriodicFiveHalvesIntegratedRoute.agda",
    "NSPeriodicConcreteBoundaryBalance.agda",
    "NSPeriodicConcreteAdaptiveChart.agda",
    "NSPeriodicConcreteRouteDecision.agda",
    "NSPeriodicObservableDerivativeAlgebra.agda",
    "NSPeriodicPacketEnergyDerivative.agda",
    "NSPeriodicPacketFractionDerivative.agda",
    "NSPeriodicGammaDerivative.agda",
    "NSPeriodicOffPacketRatioDerivative.agda",
    "NSPeriodicSizeFunctionalDerivative.agda",
    "NSCompactGammaBoundaryFaceEstimates.agda",
    "NSCompactGammaNormalizedAdaptiveFirstExit.agda",
    "NSPeriodicConcreteGalerkinFalsificationReceipt.agda",
    "NSPeriodicConcreteProofProgramStatus.agda",
    "NSPeriodicConcreteProofProgramRegression.agda",
]
FORBIDDEN = (
    "postulate",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
    "{!!}",
    "{!",
)
REQUIRED_FALSE = {
    "NSPeriodicConcreteProofProgramStatus.agda": (
        "officialCarrierInhabited = false",
        "universalFiveHalvesProved = false",
        "universalDiniInwardnessProved = false",
        "universalAllDataCoverageProved = false",
        "unconditionalPeriodicGlobalRegularityProved = false",
    ),
    "NSPeriodicFiveHalvesIntegratedRoute.agda": (
        "integratedRouteConcretePDELeavesInhabited = false",
        "integratedRouteProvesUnconditionalGlobalRegularity = false",
    ),
    "NSPeriodicConcreteRouteDecision.agda": (
        "rawMultiplierAloneAcceptedAsFarLowProof = false",
        "staticCompactGammaAdjacentContractionAccepted = false",
        "absolutePacketEnergyFloorAccepted = false",
        "selectedRoutesInhabitedOnOfficialCarrier = false",
    ),
}


def main() -> None:
    closure = ROOT / "DASHI" / "Physics" / "Closure"
    checks: dict[str, bool] = {}
    errors: list[str] = []

    for name in MODULES:
        path = closure / name
        exists = path.is_file()
        checks[f"exists:{name}"] = exists
        if not exists:
            errors.append(f"missing {path}")
            continue
        text = path.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            ok = token not in text
            checks[f"forbidden:{name}:{token}"] = ok
            if not ok:
                errors.append(f"{name} contains forbidden token {token!r}")
        for statement in REQUIRED_FALSE.get(name, ()):
            ok = statement in text
            checks[f"false:{name}:{statement}"] = ok
            if not ok:
                errors.append(f"{name} missing fail-closed statement {statement!r}")

    out = {
        "schema": "check_ns_periodic_program_surface.v1",
        "checked_modules": len(MODULES),
        "checks": checks,
        "error_count": len(errors),
        "errors": errors,
        "ok": not errors,
    }
    print(json.dumps(out, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
