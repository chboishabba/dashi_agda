#!/usr/bin/env python3
"""Fail-closed audit for the citable Yang--Mills normalization tranche.

This checks that literature metadata, criterion distinctions, beta conventions,
Schur/coercivity boundaries and OS Gram-topology requirements remain wired and
honest. It complements check_ym_clay_frontier.py; neither script replaces Agda.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanClayT2ClusterCriterionComparisonExact.agda": (
        "R. Kotecký and D. Preiss",
        '"Cluster expansion for abstract polymer models"',
        "DOI: 10.1007/BF01211762",
        "R. Fernández and A. Procacci",
        "DOI: 10.1007/s00220-007-0279-2",
        "R. Bissacot, R. Fernández and A. Procacci",
        "DOI: 10.1007/s10955-010-9956-1",
        "C. Gruber and H. Kunz",
        "DOI: 10.1007/BF01651334",
        "dobrushinBelowKP",
        "fernandezProcacciBelowDobrushin",
        "koteckyPreissImpliesDobrushin",
        "dobrushinImpliesFernandezProcacci",
        "ExtendedGruberKunzIdentification",
        "physicalExtendedGKIdentificationLevel = conditional",
    ),
    YM / "BalabanClayT2EightWayFernandezProcacciExact.agda": (
        "R. Fernández and A. Procacci",
        "DOI: 10.1007/s00220-007-0279-2",
        "R. Bissacot, R. Fernández and A. Procacci",
        "DOI: 10.1007/s10955-010-9956-1",
        "fpCliqueMajorantAtQuarter",
        "oneTwelfthSaturatesCliqueFP",
        "oneSixteenthPlusFPSlackIsOneTwelfth",
        "oneSixteenthBelowOneTwelfth",
        "activityTimesCliqueMajorantBelowQuarter",
        "physicalEightExtensionCliqueIdentificationLevel = conditional",
    ),
    YM / "BalabanClayT3OperatorSchurComplementExact.agda": (
        "E. V. Haynsworth",
        '"Determination of the inertia of a partitioned Hermitian matrix"',
        "DOI: 10.1016/0024-3795(68)90050-5",
        "operatorSchurAlgebraVersusCoercivityBoundaryLevel = machineChecked",
        "physicalFluctuationSchurInputsLevel = conditional",
    ),
    YM / "BalabanClayT3UniformFluctuationSchurExact.agda": (
        "uniformFluctuationBlockCoercive",
        "uniformFluctuationCoefficientPositive",
        "physicalUniformFluctuationInputsLevel = conditional",
    ),
    YM / "BalabanClayT3PhysicalUniformFluctuationCoercivityExact.agda": (
        "E. Eriksson",
        "viXra:2602.0051 v2",
        "T. Balaban",
        "DOI: 10.1007/BF01215757",
        "smallFieldFluctuationCoercive",
        "smallFieldCoercivityArchitecturalCorrectionLevel = machineChecked",
        "physicalSmallFieldUniformFluctuationInputsLevel = conditional",
    ),
    YM / "BalabanClayT3WardIdentityLiteratureExact.agda": (
        "J. C. Ward",
        '"An Identity in Quantum Electrodynamics"',
        "DOI: 10.1103/PhysRev.78.182",
        "Y. Takahashi",
        '"On the generalized Ward identity"',
        "DOI: 10.1007/BF02832514",
        "fluctuationIntegralWardIdentityFromReindexing",
        "localizedWardIdentityFromEquivariance",
        "physicalWardReindexingInstantiationLevel = conditional",
    ),
    YM / "BalabanClayT4BetaNormalizationConventionExact.agda": (
        "D. J. Gross and F. Wilczek",
        "DOI: 10.1103/PhysRevLett.30.1343",
        "H. D. Politzer",
        "DOI: 10.1103/PhysRevLett.30.1346",
        "R. Dashen and D. J. Gross",
        "DOI: 10.1103/PhysRevD.23.2340",
        "inverseCouplingFromBetaDerivative",
        "inverseCouplingIsElevenOverTwentyFour",
        "inverseCouplingIsBetaZeroOverEight",
        "physicalPlaquetteCoefficientIdentificationLevel = conditional",
    ),
    YM / "BalabanClayT4RunningCouplingConventionBridgeExact.agda": (
        "betaLogBlockingUsesElevenOverTwentyFour",
        "betaLogBlockingUsesBetaZeroOverEight",
        "physicalRunningCouplingCoefficientCalculationLevel = conditional",
    ),
    YM / "BalabanClayT4SUNWilsonActionConventionExact.agda": (
        "K. G. Wilson",
        '"Confinement of quarks"',
        "DOI: 10.1103/PhysRevD.10.2445",
        "R. Dashen and D. J. Gross",
        "DOI: 10.1103/PhysRevD.23.2340",
        "scaledWilsonActionDefinition",
        "scaledSUNWilsonActionGaugeInvariant",
        "oneLoopWilsonActionUsesElevenOverTwentyFour",
        "oneLoopWilsonActionUsesBetaZeroOverEight",
        "physicalWilsonPlaquetteExtractionLevel = conditional",
    ),
    YM / "BalabanDashenGrossCalibration.agda": (
        "R. Dashen and D. J. Gross",
        "DOI: 10.1103/PhysRevD.23.2340",
        "dashenGrossBibliographicConventionLevel = machineChecked",
    ),
    YM / "BalabanClayT5LimitAndNontrivialityExact.agda": (
        "K. Osterwalder and R. Schrader",
        "DOI: 10.1007/BF01645738",
        "DOI: 10.1007/BF01608978",
        "osClosureRequiresGramTopologyLevel = machineChecked",
    ),
    YM / "BalabanClayT5OSGramTopologyExact.agda": (
        "K. Osterwalder and R. Schrader",
        "DOI: 10.1007/BF01645738",
        "DOI: 10.1007/BF01608978",
        "P. Menotti and A. Pelissetto",
        "DOI: 10.1007/BF01221251",
        "gramQuadraticFormConverges",
        "continuumReflectionPositiveFromGramTopology",
        "physicalOSGramTopologyIdentificationLevel = conditional",
    ),
    YM / "BalabanClayT5OSGramClosedPropertyExact.agda": (
        "measureConvergenceImpliesGramConvergence",
        "measureReflectionPositiveClosed",
        "reflectionPositiveSequentiallyClosed",
        "physicalMeasureToOSGramContinuityLevel = conditional",
    ),
    YM / "BalabanClayLiteratureNormalizationLedger.agda": (
        "kpDobrushinFernandezProcacciHierarchyLevel = machineChecked",
        "eightWayFPCliqueArithmeticLevel = machineChecked",
        "rootedShellVersusFPConvergenceSeparationLevel = machineChecked",
        "uniformFluctuationCoercivityReductionLevel = machineChecked",
        "wardReindexingNormalizationLevel = machineChecked",
        "betaZeroOverEightEqualsElevenOverTwentyFourLevel = machineChecked",
        "scaledSUNWilsonActionConventionLevel = machineChecked",
        "osGramTopologyClosureLevel = machineChecked",
        "literalCriterionMajorantIdentificationLevel = conditional",
        "literalEightExtensionCliqueGeometryLevel = conditional",
        "literalUniformFluctuationCoercivityLevel = conditional",
        "literalWardMeasureReindexingLevel = conditional",
        "literalWilsonPlaquetteCoefficientLevel = conditional",
        "literalOSGramConvergenceLevel = conditional",
    ),
    YM / "BalabanClayConstructiveProducerAdvance.agda": (
        "BalabanClayT2EightWayFernandezProcacciExact",
        "BalabanClayT3WardIdentityLiteratureExact",
        "BalabanClayT4SUNWilsonActionConventionExact",
        "BalabanClayLiteratureNormalizationLedger",
    ),
}

FORBIDDEN = (
    (re.compile(r"(?m)^\s*postulate\b"), "postulate declaration"),
    (re.compile(r"\{\!\!\}"), "Agda hole"),
    (re.compile(r"\{-#\s*(?:NON_)?TERMINATING\s*#-\}"), "unsafe termination pragma"),
    (re.compile(r"=\s*_\s*(?:\n|$)"), "underscore proof body"),
)


def fail(message: str) -> None:
    print(f"Clay literature audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, tokens in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for pattern, label in FORBIDDEN:
            if pattern.search(text):
                fail(f"forbidden {label} in {path.relative_to(ROOT)}")
        for token in tokens:
            if token not in text:
                fail(f"missing {token!r} in {path.relative_to(ROOT)}")

    print(
        "Citable normalization tranche present: KP/Dobrushin/FP and extended-GK "
        "lanes are distinct; the eight-way FP clique insurance is separate from "
        "the stronger 1/16 rooted-shell bound; Schur algebra is separated from "
        "uniform coercivity; Ward identities come from exact reindexing; the SUN "
        "Wilson action fixes the inverse-g^2 convention; beta_0/(8 pi^2) equals "
        "11 C_A/(24 pi^2); and OS reflection positivity is closed only through "
        "complete Gram-form convergence. Literal physical leaves remain conditional."
    )


if __name__ == "__main__":
    main()
