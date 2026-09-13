#!/usr/bin/env python3
"""Focused static contract for the Penrose horismos compactness payment.

This checker is intentionally structural. It requires an explicit compactness
owner between local focusing / causal-boundary semantics and the global
compact-vs-noncompact horismos contradiction. It does not certify continuum
topology, the null exponential map, or the Penrose theorem.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COMPACTNESS = ROOT / "DASHI/Physics/Gravity/PenroseHorismosCompactnessPaymentExact.agda"
GLOBAL = ROOT / "DASHI/Physics/Gravity/PenroseGlobalHorismosContradictionExact.agda"
REGRESSION = ROOT / "DASHI/Physics/Gravity/IntrinsicPenroseInterpretationRegression.agda"
AGGREGATE = ROOT / "DASHI/Physics/PhysicsKernelClosure.agda"


def require(path: Path, needles: list[str]) -> None:
    if not path.exists():
        raise SystemExit(f"missing required file: {path.relative_to(ROOT)}")
    text = path.read_text(encoding="utf-8")
    missing = [needle for needle in needles if needle not in text]
    if missing:
        raise SystemExit(f"{path.relative_to(ROOT)} missing required surfaces: {missing}")

require(COMPACTNESS, [
    "compactTrappedSurfaceCarrier",
    "continuousStrictNegativeNullExpansion",
    "compactnessPaysUniformNegativeExpansionMargin",
    "uniformAffineFocusingBound",
    "futureNullNormalDirectionFibreCompact",
    "boundedGeneratorParameterDomainCompact",
    "nullExponentialGeneratorMapContinuous",
    "futureHorismosCoveredByBoundedGeneratorImage",
    "futureHorismosClosedUnderGlobalHyperbolicity",
    "compactParameterImagePaysHorismosCompactness",
    "pointwiseNegativeExpansionDoesNotAloneGiveUniformBound",
    "rawNullNormalVectorFibreIsNotCompactDirectionFibre",
    "boundedAffineParameterDoesNotAloneMakeHorismosCompact",
    "compactnessOwnerInternallyReprovesContinuumTopology",
])
require(GLOBAL, [
    "horismosCompactnessConsumer",
    "nullCompletenessPlusFocusingMakesFutureHorismosCompact",
])
require(REGRESSION, [
    "pointwiseNegativeNotUniformRegression",
    "rawNullVectorFibreFirewallRegression",
    "boundedParameterNotCompactnessRegression",
    "compactnessTopologyDerivationStillClosedRegression",
])
require(AGGREGATE, ["PenroseHorismosCompactnessPaymentExact"])

print("Penrose horismos compactness payment static contract: OK")
