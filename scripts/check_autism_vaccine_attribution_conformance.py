#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

conformance = ROOT / "DASHI/Biology/AutismVaccineAttributionRuleConformanceExact.agda"
regression = ROOT / "DASHI/Biology/AutismVaccineAttributionRuleConformanceRegression.agda"
sota = ROOT / "DASHI/Biology/AutismVaccineCurrentSOTA2026Exact.agda"
sota_regression = ROOT / "DASHI/Biology/AutismVaccineCurrentSOTA2026Regression.agda"
rollup = ROOT / "DASHI/Biology/AutismVaccineAuditEverything.agda"
strict = ROOT / "DASHI/Biology/AutismVaccineStrictBindingInstantiationExact.agda"

for path in [conformance, regression, sota, sota_regression, rollup, strict]:
    assert path.exists(), f"missing autism-vaccine attribution surface: {path}"

conformance_text = conformance.read_text()
regression_text = regression.read_text()
sota_text = sota.read_text()
rollup_text = rollup.read_text()
strict_text = strict.read_text()

for needle in [
    "scientificSupportProvesPriority",
    "priorityProvesCorrectness",
    "contactOrExposureProvesDerivation",
    "contactOrExposureProvesPlagiarism",
    "unknownCoordinateEqualsZero",
    "unpaidCoordinateEqualsZero",
    "externalSourceOwnsDASHISynthesis",
    "strictSameObjectSameEstimandBindingPresent",
    "canonicalHviidEvidenceClaimWitness",
    "canonicalHviidEstimandWitness",
]:
    assert needle in conformance_text, f"conformance boundary missing {needle}"

for needle in [
    "supportPriorityCorrectnessRemainSeparateRegression",
    "contactExposureDoesNotBecomeDerivationRegression",
    "unknownAndUnpaidDoNotBecomeZeroRegression",
    "sourceAndDASHISynthesisRemainSeparateRegression",
    "hviidTypedClaimPaymentIsActuallyConsumed",
    "hviidTypedEstimandMatchIsActuallyConsumed",
]:
    assert needle in regression_text, f"conformance regression missing {needle}"

for needle in [
    "World Health Organization",
    "Vaccines, thiomersal and autism spectrum disorder: evidence review 2010-2025",
    "broaderReviewAutomaticallyPaysExactHbombMMREstimand",
    "reviewCreatesUniversalZeroRiskTheorem",
]:
    assert needle in sota_text, f"2026 SOTA boundary missing {needle}"

for needle in [
    "hviidPaysHbombNoLinkClaim",
    "cochranePaysHbombNoLinkClaim",
    "mmrAutismPopulationEstimand",
    "mmrAutismReviewEstimand",
]:
    assert needle in strict_text, f"strict autism-vaccine binding missing {needle}"

for needle in [
    "AutismVaccineAttributionRuleConformanceExact",
    "AutismVaccineAttributionRuleConformanceRegression",
    "AutismVaccineCurrentSOTA2026Exact",
    "AutismVaccineCurrentSOTA2026Regression",
]:
    assert needle in rollup_text, f"autism-vaccine rollup missing {needle}"

print("autism-vaccine attribution + current-SOTA conformance static contract: PASS")
