#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = [
    "DASHI/Chemistry/GoldReactionReplaySuiteExact.agda",
    "DASHI/Biology/LeadCalciumEndToEndReplayExact.agda",
    "DASHI/Biology/KitzerowBH4FluxCausalModelsExact.agda",
    "DASHI/Chemistry/LineageBidiDiscriminatorSynthesisExact.agda",
    "DASHI/Biology/CarbonSiliconReachableChemistryBenchmarkExact.agda",
    "DASHI/Chemistry/LineageCalibrationAttributionEnvelopeExact.agda",
    "DASHI/Chemistry/LineageSourceManifestationGuardExact.agda",
    "DASHI/Chemistry/LineageAttributionAcquisitionFrontierExact.agda",
    "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
    "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
]
for rel in required:
    assert (ROOT / rel).exists(), f"missing {rel}"

gold = (ROOT / required[0]).read_text()
for needle in [
    "chlorAlkaliReplay", "pahReplay", "dhprReplay", "pbCaReplay", "carbonBondReplay",
    "atomLineageExplicit", "electronAuditExplicit", "completeMicroscopicMechanismProved",
]:
    assert needle in gold, f"gold replay suite missing {needle}"

pbca = (ROOT / required[1]).read_text()
for needle in [
    "LeadCalciumAtomicLineageRegressionExact", "coordinationGeometryReference",
    "firstSeparatingCoordinateReference", "atomicIdentityCollapsed",
    "targetLocalSubstitutionProvesOrganismEquivalence",
]:
    assert needle in pbca, f"Pb/Ca end-to-end replay missing {needle}"

bh4 = (ROOT / required[2]).read_text()
for needle in [
    "d[BH4]/dt = J_synth + J_recycle", "J_PAH", "J_NOS", "J_AGMO",
    "upstreamAllocator", "downstreamConsequence", "parallelRedoxMarker", "contextSpecificSubgroup",
    "numericBranchFluxCalibrated", "symbolicMassBalanceProvesAllocatorModel",
]:
    assert needle in bh4, f"BH4 flux/causal owner missing {needle}"

disc = (ROOT / required[3]).read_text()
for needle in [
    "ModelDiscriminationProblem", "synthesizeCandidate", "canonicalBH4AllocatorVsParallelCandidate",
    "canonicalPbCaFunctionalCandidate", "generatedCandidateCreatesTruth",
]:
    assert needle in disc, f"discriminator synthesis missing {needle}"

carbon = (ROOT / required[4]).read_text()
for needle in [
    "carbonReceipt", "siliconReceipt", "matchedPrebioticEnvironment", "reachableConeComparisonExplicit",
    "carbonPredeclaredWinner", "carbonWinsImpliesLifeInevitable",
]:
    assert needle in carbon, f"carbon/silicon benchmark missing {needle}"

attribution = (ROOT / required[5]).read_text()
for needle in [
    "AttributedSourceCore", "SnowballAttributionProvenanceInvariantExact",
    "ReplayAttributionEnvelope", "chlorAlkaliEuroChlor2022", "pahMechanismSource",
    "dhprBrenda2026", "pbCaGeometrySource", "astrobiologyPrimer2016",
    "sourceOwnsDashiComposition", "citationCreatesNumericPayment",
    "dashiSynthesisAttributedToExternalSource", "sourceObservationAttributedToDashi",
]:
    assert needle in attribution, f"attribution envelope missing {needle}"

manifestation = (ROOT / required[6]).read_text()
for needle in [
    "SourceCoordinateGuard", "ManifestationStatus", "LocatorStatus", "CoordinateRole",
    "sameObjectAndLocatorRequiredForNumericPayment", "nearbyCitationPaysCoordinate",
    "crossSourceAnalogyPaysSameObjectClaim", "carbonSpecificReactionGuard",
]:
    assert needle in manifestation, f"manifestation guard missing {needle}"

acquisition = (ROOT / required[7]).read_text()
for needle in [
    "bh4FluxDataset", "pahAtomMap", "chlorLocator", "pbCaTargetDataset",
    "carbonSiliconMatchedDataset", "frontierRankIsTruthRank",
    "unpaidCoordinateRetainsAttribution", "causalValueSeparateFromAttributionValue",
]:
    assert needle in acquisition, f"attribution acquisition frontier missing {needle}"

rollup = (ROOT / required[8]).read_text()
for needle in [
    "LineageCalibrationAttributionEnvelopeExact",
    "LineageSourceManifestationGuardExact",
    "LineageAttributionAcquisitionFrontierExact",
]:
    assert needle in rollup, f"rollup missing {needle}"

full = (ROOT / "DASHI/Chemistry/EverythingFull.agda").read_text()
assert "LineageCalibrationDiscriminatorEverything" in full

kit = (ROOT / "DASHI/Biology/KitzerowBH4Everything.agda").read_text()
assert "KitzerowBH4FluxCausalModelsExact" in kit

print("lineage calibration discriminator + attribution max-cut static contract: PASS")
