#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "DASHI/Biology/IBSTrialDesignDonorAtlasExact.agda",
    ROOT / "DASHI/Biology/IBSTrialDesignDonorAtlasRegression.agda",
    ROOT / "DASHI/Biology/IBSAdaptiveBeliefPolicyExact.agda",
    ROOT / "DASHI/Biology/IBSAdaptiveBeliefPolicyRegression.agda",
    ROOT / "DASHI/Biology/IBSPersonalizationValidationExact.agda",
    ROOT / "DASHI/Biology/IBSPersonalizationValidationRegression.agda",
    ROOT / "DASHI/Biology/IBSMonashAdaptiveSequencingExact.agda",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "canonicalIBSTrialDesignDonorAtlas",
    "canonicalInitialIBSBeliefState",
    "canonicalAdaptivePolicyParetoFrontier",
    "canonicalIBSPersonalizationValidationAtlas",
    "10.1016/j.amepre.2007.01.022",
    "10.1002/sim.8737",
    "10.1016/j.cgh.2021.12.016",
    "10.1053/j.gastro.2026.08.026",
    "10.1111/apt.70601",
    "10.14309/ajg.0000000000002862",
    "10.1080/19490976.2026.2719125",
    "smartDesignDoesNotProveIBSEfficacy",
    "cleReactionDoesNotValidateFoodTarget",
    "singleResponseDoesNotMakeRegimeTrue",
    "numericPosteriorRequiresValidatedLikelihood",
    "personalizedLabelDoesNotImplySuperiorOutcome",
    "mechanisticBiomarkerDoesNotBecomeValidatedSelector",
    "internalPersonalizationModelDoesNotAutomaticallyTransport",
    "SI genotype negative-stratification",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing IBS adaptive policy surface: " + ", ".join(missing))
forbidden = [
    "personalized always superior",
    "CLE proves trigger",
    "SMART proves IBS efficacy",
    "this patient has causal regime",
    "numeric posterior =",
    "SI genotype as candidate modifier",
]
found = [x for x in forbidden if x in text]
if found:
    raise SystemExit("forbidden IBS adaptive promotion surface: " + ", ".join(found))
print("IBS adaptive policy/personalization source surface: OK")
