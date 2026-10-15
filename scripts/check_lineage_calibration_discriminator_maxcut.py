#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = [
    "DASHI/Chemistry/GoldReactionReplaySuiteExact.agda",
    "DASHI/Biology/LeadCalciumEndToEndReplayExact.agda",
    "DASHI/Biology/KitzerowBH4FluxCausalModelsExact.agda",
    "DASHI/Chemistry/LineageBidiDiscriminatorSynthesisExact.agda",
    "DASHI/Biology/CarbonSiliconReachableChemistryBenchmarkExact.agda",
    "DASHI/Chemistry/LineageAttributionEvidenceSourceAtlasExact.agda",
    "DASHI/Chemistry/LineageAttributionEvidencePaymentExact.agda",
    "DASHI/Chemistry/AttributedGoldReactionReplayExact.agda",
    "DASHI/Chemistry/LineageQuantitativeCalibrationLedgerExact.agda",
    "DASHI/Chemistry/LineageAttributionAcquisitionParetoExact.agda",
    "DASHI/Chemistry/LineageAttributionEvidenceMaxCutValidation.agda",
    "DASHI/Chemistry/LineageCalibrationAttributionEnvelopeExact.agda",
    "DASHI/Chemistry/LineageSourceManifestationGuardExact.agda",
    "DASHI/Chemistry/LineageAttributionAcquisitionFrontierExact.agda",
    "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
    "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
]
for rel in required:
    assert (ROOT / rel).exists(), f"missing {rel}"

for needle in ["chlorAlkaliReplay", "pahReplay", "dhprReplay", "pbCaReplay", "carbonBondReplay"]:
    assert needle in (ROOT / required[0]).read_text(), f"gold replay suite missing {needle}"

source_atlas = (ROOT / required[5]).read_text()
for needle in [
    "AttributedSourceCore", "chlorAlkaliBREF2014", "astrobiologyPrimer2016",
    "canonicalLineageCalibrationSourceAtlas", "canonicalAtlasNonPromoting",
]:
    assert needle in source_atlas, f"canonical source atlas missing {needle}"

payment = (ROOT / required[6]).read_text()
for needle in [
    "SourceCoordinatePayment", "sourceOwnsDASHISynthesis", "citationCreatesProof",
    "citationAlonePaysCalibration", "missingCoordinatePromotedByNearbyCitation",
    "exactLocatorRequiredForNumericPromotion",
]:
    assert needle in payment, f"evidence payment owner missing {needle}"

replay = (ROOT / required[7]).read_text()
for needle in [
    "AttributedGoldReplay", "canonicalAttributedGoldReplays", "sourceOwnsReplayComposition",
    "replayCompositionErasesSourceIdentity", "unpaidCoordinatesRemainAttributed",
]:
    assert needle in replay, f"attributed replay owner missing {needle}"

calibration = (ROOT / required[8]).read_text()
for needle in [
    "QuantitativeCalibrationCell", "bh4BranchFluxCell", "pahKineticCell", "chlorElectrodeCell",
    "pbCaAffinityCell", "carbonSiliconYieldCell", "numberWithoutExactLocatorPromoted",
    "numberWithoutContextPromoted", "unpaidCoordinateInterpretedAsZero",
]:
    assert needle in calibration, f"quantitative calibration ledger missing {needle}"

pareto = (ROOT / required[9]).read_text()
for needle in [
    "bh4SameObjectFluxDataset", "isotopeAtomMapBenchmarks", "pbCaTargetCalibration",
    "carbonSiliconMatchedDataset", "frontierRankIsTruthRank", "selectionCreatesEvidence",
]:
    assert needle in pareto, f"canonical scientific acquisition Pareto missing {needle}"

attribution = (ROOT / required[11]).read_text()
for needle in [
    "LineageAttributionEvidenceSourceAtlasExact", "ReplayAttributionEnvelope",
    "chlorAlkaliTechnicalSource", "pahMechanismSource", "dhprBrenda2026", "pbCaGeometrySource",
    "astrobiologyPrimerSource", "canonicalSourceAtlasReusedWhereAvailable",
    "citationCreatesNumericPayment", "dashiSynthesisAttributedToExternalSource",
    "sourceObservationAttributedToDashi",
]:
    assert needle in attribution, f"attribution envelope missing {needle}"

manifestation = (ROOT / required[12]).read_text()
for needle in [
    "SourceCoordinateGuard", "ManifestationStatus", "LocatorStatus", "CoordinateRole",
    "sameObjectAndLocatorRequiredForNumericPayment", "nearbyCitationPaysCoordinate",
    "crossSourceAnalogyPaysSameObjectClaim", "carbonSpecificReactionGuard",
]:
    assert needle in manifestation, f"manifestation guard missing {needle}"

acquisition = (ROOT / required[13]).read_text()
for needle in [
    "LineageAttributionAcquisitionParetoExact", "scientificAcquisitionFrontier",
    "stanfordContactArtifact", "brazilCorrespondenceArtifact", "iaccMedMapsContactArtifact",
    "canonicalScientificParetoReused", "scientificSupportSeparateFromContactProvenance",
    "contactEvidenceAutomaticallyProvesDerivation", "contactEvidenceAutomaticallyProvesPlagiarism",
    "scientificSupportAutomaticallyProvesPriority", "frontierRankIsTruthRank",
]:
    assert needle in acquisition, f"contact provenance extension missing {needle}"

rollup = (ROOT / required[14]).read_text()
for needle in [
    "LineageAttributionEvidenceSourceAtlasExact", "LineageAttributionEvidencePaymentExact",
    "AttributedGoldReactionReplayExact", "LineageQuantitativeCalibrationLedgerExact",
    "LineageAttributionAcquisitionParetoExact", "LineageAttributionEvidenceMaxCutValidation",
    "LineageCalibrationAttributionEnvelopeExact", "LineageSourceManifestationGuardExact",
    "LineageAttributionAcquisitionFrontierExact",
]:
    assert needle in rollup, f"rollup missing {needle}"

validation = (ROOT / required[15]).read_text()
for needle in [
    "attributionEnvelopeRetainsSourceRoleWithoutPromotion",
    "manifestationGuardBlocksNearbySourcePromotion",
    "contactProvenanceDoesNotCollapseIntoScientificOrDerivationEvidence",
]:
    assert needle in validation, f"validation missing {needle}"

full = (ROOT / "DASHI/Chemistry/EverythingFull.agda").read_text()
assert "LineageCalibrationDiscriminatorEverything" in full
kit = (ROOT / "DASHI/Biology/KitzerowBH4Everything.agda").read_text()
assert "KitzerowBH4FluxCausalModelsExact" in kit

print("lineage calibration/discriminator + unified attribution/evidence max-cut static contract: PASS")
