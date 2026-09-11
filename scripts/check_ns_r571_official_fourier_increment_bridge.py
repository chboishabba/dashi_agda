#!/usr/bin/env python3
"""Source-level regression contract for the R571 homochiral Fourier/increment splice.

Timestamp: 2026-09-11 20:46 AEST (UTC+10).

This checker is intentionally fail-closed.  It requires two thin production owners:
  * official periodic torus-character/Fourier realization;
  * R571 homochiral radial same-object specialization.

It does not certify the still-open radial-near analytic gain or R568.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

OFFICIAL = ROOT / "DASHI/Physics/Closure/NSTriadKNOfficialPeriodicTorusCharacterIntegralExact.agda"
R571 = ROOT / "DASHI/Physics/Closure/NSTriadKNR571HomochiralRadialIncrementSpecializationExact.agda"
AGG = ROOT / "DASHI/Physics/Closure/NSTriadKNLiteralR406DirectAnalyticFrontierEverythingRound569Exact.agda"


def require(path: Path, needles: tuple[str, ...]) -> None:
    if not path.exists():
        raise SystemExit(f"missing required file: {path.relative_to(ROOT)}")
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            raise SystemExit(f"{path.relative_to(ROOT)} missing required token: {needle}")


require(
    OFFICIAL,
    (
        "module DASHI.Physics.Closure.NSTriadKNOfficialPeriodicTorusCharacterIntegralExact where",
        "TorusCharacterIntegral",
        "polynomialCoefficientExtraction",
        "finiteWeightedIncrementEqualsPairMultiplier",
        "officialPeriodicTorusCharacterIntegralRealizationClosed",
        "officialPeriodicHaarBochnerRealizationStandardImported",
    ),
)

require(
    R571,
    (
        "module DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact where",
        "samePlusDifference",
        "sameMinusDifference",
        "translationMultiplierCommutatorExact",
        "r571HomochiralRadialCarrierWeldClosed",
        "r571RadialNearAnalyticGainClosed = false",
        "r571HeterochiralPromotionIntroduced = false",
    ),
)

require(
    AGG,
    (
        "NSTriadKNOfficialPeriodicTorusCharacterIntegralExact",
        "NSTriadKNR571HomochiralRadialIncrementSpecializationExact",
    ),
)

print("R571 official Fourier/increment bridge source contract: PASS")
