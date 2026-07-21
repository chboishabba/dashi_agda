#!/usr/bin/env python3
"""Fail-closed audit for the constructive Yang-Mills submission spine.

This script checks repository integrity only. It does not certify any analytic
estimate. Its purpose is to prevent a missing theorem name, proof escape, or
manual Boolean promotion from silently presenting the current conditional spine
as an unconditional solution.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI" / "Physics" / "YangMills"
SPINE = YM / "BalabanClayAnalyticInhabitationSpine.agda"
GATE = YM / "BalabanUnconditionalSolutionCertificate.agda"

FORBIDDEN = {
    "postulate": re.compile(r"^\s*postulate\b", re.MULTILINE),
    "unsolved hole": re.compile(r"\{!!\}"),
    "terminating escape": re.compile(r"\{-#\s*TERMINATING\s*#-\}"),
    "non-terminating escape": re.compile(r"\{-#\s*NON_TERMINATING\s*#-\}"),
}

REQUIRED_THEOREMS = (
    "bulkGaugeFixedHodgePoincare",
    "uniformConstrainedHessianCoercive",
    "bulkWeightedGreenBound",
    "bulkWeightedGradientGreenBound",
    "bulkWeightedSecondGradientGreenBound",
    "qCommonStrict",
    "uniformNonlinearRemainderLipschitz",
    "greenTimesNonlinearBelowRho",
    "rhoGStrict",
    "oneStepPolymerContraction",
    "concreteKoteckyPreiss",
    "effectiveActionUniformAtEveryScale",
    "infiniteVolumeLimitUnique",
    "continuumLimitUnique",
    "reflectionPositivityClosedUnderSchwingerLimit",
    "connectedFourPointFunctionSurvives",
    "uniformConnectedCorrelationDecay",
    "exponentialTimeClusteringImpliesSpectrumGap",
)

SOURCE_AUTHORITY_FILES = (
    YM / "BalabanPublishedAnalyticAuthorities.agda",
    YM / "BalabanPublishedSourceTheoremAuthorities.agda",
    YM / "BalabanExactPublishedCarrierMatching.agda",
    YM / "BalabanPublishedSourceToDashi.agda",
)

REDUCTION_AND_REGRESSION_FILES = (
    YM / "BalabanFiniteFourierHodgeReduction.agda",
    YM / "BalabanFiniteFourierHodgeReductionRegression.agda",
    YM / "BalabanPublishedSourceTheoremRegression.agda",
    YM / "BalabanExactPublishedCarrierMatchingRegression.agda",
)

AUDITED_NEW_FILES = SOURCE_AUTHORITY_FILES + REDUCTION_AND_REGRESSION_FILES + (
    GATE,
    SPINE,
)


def fail(message: str) -> None:
    print(f"YM unconditional gate: FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def read(path: pathlib.Path) -> str:
    if not path.is_file():
        fail(f"missing required file: {path.relative_to(ROOT)}")
    return path.read_text(encoding="utf-8")


def main() -> None:
    for path in AUDITED_NEW_FILES:
        text = read(path)
        for label, pattern in FORBIDDEN.items():
            if pattern.search(text):
                fail(f"{label} found in {path.relative_to(ROOT)}")

    all_agda = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted(YM.glob("*.agda"))
    )
    missing = [name for name in REQUIRED_THEOREMS if name not in all_agda]
    if missing:
        fail("missing load-bearing theorem names: " + ", ".join(missing))

    spine = read(SPINE)
    if "clayYangMillsSubmissionPromoted = false" not in spine:
        fail("repository-level submission promotion is not explicitly fail-closed")
    if re.search(r"clayYangMillsSubmissionPromoted\s*=\s*true", spine):
        fail("manual true submission promotion detected")

    required_open_levels = {
        "finiteFourierAndSymbolGapInputLevel": "conditional",
        "bulkFiniteBackgroundInputLevel": "conditional",
        "publishedCarrierMatchingLevel": "conditional",
        "patchTransferInputLevel": "conditional",
        "oneStepAndAllScaleInputLevel": "conditional",
        "thermodynamicInputLevel": "conditional",
        "continuumOSInputLevel": "conjectural",
        "physicalMassGapInputLevel": "conjectural",
        "unconditionalSolutionInhabitationLevel": "conjectural",
    }
    for name, level in required_open_levels.items():
        assignment = re.compile(rf"{re.escape(name)}\s*=\s*{level}\b")
        if not assignment.search(spine):
            fail(f"expected fail-closed status `{name} = {level}` not found")

    gate = read(GATE)
    required_gate_fields = (
        "solutionForEveryCompactSimpleGaugeGroup",
        "finiteVolumeConstruction",
        "uniformRenormalizedSchwingerBounds",
        "thermodynamicLimitExists",
        "thermodynamicLimitUnique",
        "continuumLimitExists",
        "continuumLimitUnique",
        "quantumYangMillsTheoryOnR4",
        "continuumOSAxioms",
        "continuumTheoryNonGaussian",
        "uniformConnectedCorrelationDecay",
        "positiveClusteringRate",
        "physicalHamiltonianMassGap",
        "noConditionalLeafOnFinalPath",
        "noConjecturalLeafOnFinalPath",
        "importedAuthoritiesHypothesesMatch",
        "officialJaffeWittenStatementMatched",
    )
    missing_gate = [name for name in required_gate_fields if name not in gate]
    if missing_gate:
        fail("terminal certificate is missing fields: " + ", ".join(missing_gate))

    for path in SOURCE_AUTHORITY_FILES:
        text = read(path)
        if "ProofLevel" not in text:
            fail(f"missing proof-level boundary in {path.relative_to(ROOT)}")

    source_regression = read(
        YM / "BalabanPublishedSourceTheoremRegression.agda"
    )
    for name in (
        "propagatorSourceConversionRegression",
        "variationalSourceConversionRegression",
        "smallFieldSourceConversionRegression",
    ):
        if name not in source_regression:
            fail(f"source theorem regression missing `{name}`")

    matching_regression = read(
        YM / "BalabanExactPublishedCarrierMatchingRegression.agda"
    )
    for name in (
        "propagatorBoundRegression",
        "backgroundCriticalRegression",
        "smallFieldRGRegression",
    ):
        if name not in matching_regression:
            fail(f"exact matching regression missing `{name}`")

    hodge_regression = read(
        YM / "BalabanFiniteFourierHodgeReductionRegression.agda"
    )
    for name in ("bulkHodgeRegression", "uniformHodgeRegression"):
        if name not in hodge_regression:
            fail(f"finite Fourier Hodge regression missing `{name}`")

    print("YM unconditional gate: PASS")
    print(f"  audited files: {len(AUDITED_NEW_FILES)}")
    print(f"  load-bearing theorem names present: {len(REQUIRED_THEOREMS)}")
    print("  official all-compact-simple-groups quantifier present")
    print("  source theorem conversion regression present")
    print("  exact published-carrier regression present")
    print("  finite Fourier Hodge regression present")
    print("  repository submission promotion remains false")
    print("  unresolved analytic levels remain explicit")


if __name__ == "__main__":
    main()
