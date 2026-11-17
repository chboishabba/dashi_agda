#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

strict = ROOT / "DASHI/Biology/StrictEvidencePromotionBindingExact.agda"
bh4 = ROOT / "DASHI/Biology/KitzerowBH4StrictEvidenceBindingExact.agda"
validation = ROOT / "DASHI/Biology/KitzerowBH4StrictEvidenceBindingValidation.agda"
kit_rollup = ROOT / "DASHI/Biology/KitzerowBH4Everything.agda"
chem_rollup = ROOT / "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda"

for path in [strict, bh4, validation, kit_rollup, chem_rollup]:
    assert path.exists(), f"missing strict-binding surface: {path}"

strict_text = strict.read_text()
bh4_text = bh4.read_text()
validation_text = validation.read_text()
kit_text = kit_rollup.read_text()
chem_text = chem_rollup.read_text()

for needle in [
    "evidencePaysClaimWitness",
    "evidenceMatchesEstimandWitness",
    "boundClaimKeyMatches",
    "boundEvidenceKeyMatches",
    "boundEstimandScopeKeyMatches",
]:
    assert needle in strict_text, f"generic strict binding missing {needle}"

for needle in [
    "cacoStrictBinding",
    "thStrictBinding",
    "tphStrictBinding",
    "routeStateStrictBinding",
    "cacoRatePaysTargetNeuralDonorRecipientFlux",
    "separateBranchStudiesPaySameObjectSimultaneousAllocation",
    "sameClaimLabelErasesEstimandScope",
    "strictBindingsCloseWholeAllocator",
    "There are deliberately no EvidencePaysClaim or EvidenceMatchesEstimand",
]:
    assert needle in bh4_text, f"BH4 strict binding missing {needle}"

for needle in [
    "cacoRateCannotPayTargetNeuralFlux",
    "separateTHAndTPHStudiesDoNotPaySimultaneousAllocation",
    "sameClaimLabelDoesNotEraseEstimandScope",
    "strictBindingsDoNotCloseWholeAllocator",
]:
    assert needle in validation_text, f"BH4 strict validation missing {needle}"

for text, label in [(kit_text, "Kitzerow rollup"), (chem_text, "chemistry rollup")]:
    for needle in [
        "StrictEvidencePromotionBindingExact",
        "KitzerowBH4StrictEvidenceBindingExact",
        "KitzerowBH4StrictEvidenceBindingValidation",
    ]:
        assert needle in text, f"{label} missing {needle}"

print("BH4 strict evidence->claim->estimand max-cut static contract: PASS")
