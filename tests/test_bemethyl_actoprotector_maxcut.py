from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Physics/Chemistry/BemethylChemicalIdentityBoundaryExact.agda": [
        "module DASHI.Physics.Chemistry.BemethylChemicalIdentityBoundaryExact where",
        "neutralFormula = \"C9H10N2S\"",
        "isPurineBase = false",
        "structuralSimilarityProvesGenomicTarget = false",
        "saltIdentityEqualsNeutralIdentity = false",
    ],
    "DASHI/Biology/BemethylActoprotectorClaimAtlasExact.agda": [
        "module DASHI.Biology.BemethylActoprotectorClaimAtlasExact where",
        "mechanismResolved = false",
        "purineSimilarityProvesDNABinding = false",
        "historicalUseProvesEfficacy = false",
    ],
    "DASHI/Biology/BemethylMetabolicMechanismBoundaryExact.agda": [
        "module DASHI.Biology.BemethylMetabolicMechanismBoundaryExact where",
        "CoriCycleRoute",
        "MitochondrialEnzymeRoute",
        "AntioxidantEnzymeRoute",
        "proteinSynthesisDependenceDoesNotIdentifyTarget = refl",
    ],
    "DASHI/Biology/BemethylMechanismInterventionAcquisitionExact.agda": [
        "module DASHI.Biology.BemethylMechanismInterventionAcquisitionExact where",
        "actinomycinDInterventionObserved = true",
        "protectiveEffectDependsOnTranscriptionCompatibleProcess = true",
        "interventionIdentifiesDirectBemethylTarget = false",
        "gstDockingIsMetabolismEvidenceNotActoprotectionTarget = refl",
    ],
    "DASHI/Biology/BemethylBioenergeticCrossPollinationExact.agda": [
        "module DASHI.Biology.BemethylBioenergeticCrossPollinationExact where",
        "existingATPAdapter",
        "sameObjectHumanValidationPaid = false",
        "mechanismHypothesisDoesNotUpgradeExistingATPTheorem = refl",
        "chemicalSimilarityDoesNotPayMechanism = refl",
    ],
    "DASHI/Biology/BemethylHumanEvidenceAcquisitionExact.agda": [
        "module DASHI.Biology.BemethylHumanEvidenceAcquisitionExact where",
        "heatExertionDoubleBlindControlled = true",
        "operatorPerformancePlaceboControlled = true",
        "healthyVolunteerPKSingleOralDoseMg = \"250\"",
        "humanExcretionExposureObserved = true",
        "recurrentErysipelasPlaceboControlled = true",
        "humanTargetEngagementPaid = false",
        "modernPerformanceReplicationPaid = false",
    ],
    "DASHI/Biology/BemethylParetoSnowballExact.agda": [
        "module DASHI.Biology.BemethylParetoSnowballExact where",
        "targetEngagementPriority = 5",
        "modernPerformancePriority = 4",
        "heatOxygenPriority = 3",
        "humanPKPriority = 2",
        "historicalUsePriority = 1",
        "historicalControlledPerformanceEvidenceNowAcquired = true",
        "transcriptionDependenceEvidenceNowAcquired = true",
        "reviewRepetitionDoesNotIncreaseAuthority = refl",
    ],
    "DASHI/Biology/BemethylActoprotectorMaxCutExact.agda": [
        "module DASHI.Biology.BemethylActoprotectorMaxCutExact where",
        "transcriptFormalised = true",
        "controlledHumanHeatEvidenceAcquired = true",
        "historicalControlledPerformanceEvidenceAcquired = true",
        "humanExposureEvidenceAcquired = true",
        "humanPKParameterEvidenceAcquired = true",
        "transcriptionDependentMechanismEvidenceAcquired = true",
        "modernMechanismTargetIdentified = false",
        "modernHumanPerformanceReplicationPaid = false",
        "clinicalRecommendationPaid = false",
    ],
}

for rel, markers in REQUIRED.items():
    text = (ROOT / rel).read_text()
    for marker in markers:
        assert marker in text, (rel, marker)

rollup = (ROOT / "DASHI/Biology/BemethylActoprotectorEverything.agda").read_text()
for owner in REQUIRED:
    module = owner.removesuffix(".agda").replace("/", ".")
    assert f"import {module}" in rollup
