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
    "AttributedSourceCore", "LineageCalibrationAttributionEnvelopeExact",
    "chlorAlkaliBREF2014", "dhprBRENDA", "astrobiologyPrimer2016",
    "canonicalLineageCalibrationSourceAtlas", "canonicalAtlasNonPromoting",
]:
    assert needle in source_atlas, f"source atlas missing {needle}"

payment = (ROOT / required[6]).read_text()
for needle in [
    "SourceCoordinatePayment", "EvidenceRole", "PaymentGrade",
    "dhprReactionPayment", "sourceOwnsDASHISynthesis", "citationCreatesProof",
    "citationAlonePaysCalibration", "missingCoordinatePromotedByNearbyCitation",
    "reviewCountsAsPrimaryExperimentByDefault", "databaseReactionIdentityCountsAsInVivoFlux",
    "exactLocatorRequiredForNumericPromotion",
]:
    assert needle in payment, f"evidence payment owner missing {needle}"

replay = (ROOT / required[7]).read_text()
for needle in [
    "AttributedGoldReplay", "canonicalAttributedGoldReplays", "sourceOwnsReplayComposition",
    "replayCompositionErasesSourceIdentity", "unpaidCoordinatesRemainAttributed",
    "dashiAndExternalOwnershipRemainDistinct",
]:
    assert needle in replay, f"attributed replay owner missing {needle}"

calibration = (ROOT / required[8]).read_text()
for needle in [
    "QuantitativeCalibrationCell", "bh4BranchFluxCell", "pahKineticCell", "chlorElectrodeCell",
    "pbCaAffinityCell", "carbonSiliconYieldCell", "numberWithoutExactLocatorPromoted",
    "numberWithoutContextPromoted", "unpaidCoordinateInterpretedAsZero",
    "exactUnitsAndUncertaintyRemainRequired",
]:
    assert needle in calibration, f"quantitative calibration ledger missing {needle}"

attribution = (ROOT / required[10]).read_text()
for needle in [
    "ReplayAttributionEnvelope", "chlorAlkaliEuroChlor2022", "pahMechanismSource",
    "dhprBrenda2026", "pbCaGeometrySource", "astrobiologyPrimer2016",
    "citationCreatesNumericPayment", "dashiSynthesisAttributedToExternalSource",
    "sourceObservationAttributedToDashi",
]:
    assert needle in attribution, f"attribution envelope missing {needle}"

manifestation = (ROOT / required[11]).read_text()
for needle in [
    "SourceCoordinateGuard", "ManifestationStatus", "LocatorStatus", "CoordinateRole",
    "sameObjectAndLocatorRequiredForNumericPayment", "nearbyCitationPaysCoordinate",
    "crossSourceAnalogyPaysSameObjectClaim", "carbonSpecificReactionGuard",
]:
    assert needle in manifestation, f"manifestation guard missing {needle}"

acquisition = (ROOT / required[12]).read_text()
for needle in [
    "ScientificAcquisitionItem", "ProvenanceAcquisitionItem",
    "bh4FluxDataset", "pahAtomMap", "bh4KineticSet", "chlorLocator",
    "pbCaTargetDataset", "carbonSiliconMatchedDataset",
    "stanfordContactArtifact", "brazilCorrespondenceArtifact", "iaccMedMapsContactArtifact",
    "scientificSupportSeparateFromContactProvenance",
    "contactEvidenceAutomaticallyProvesDerivation", "contactEvidenceAutomaticallyProvesPlagiarism",
    "scientificSupportAutomaticallyProvesPriority", "priorityAutomaticallyProvesCorrectness",
    "frontierRankIsTruthRank", "unpaidCoordinateRetainsAttribution", "acquisitionCreatesAuthority",
]:
    assert needle in acquisition, f"unified acquisition frontier missing {needle}"

rollup = (ROOT / required[13]).read_text()
for needle in [
    "LineageCalibrationAttributionEnvelopeExact", "LineageAttributionEvidenceSourceAtlasExact",
    "LineageAttributionEvidencePaymentExact", "AttributedGoldReactionReplayExact",
    "LineageSourceManifestationGuardExact", "LineageQuantitativeCalibrationLedgerExact",
    "LineageAttributionAcquisitionFrontierExact", "LineageAttributionEvidenceMaxCutValidation",
]:
    assert needle in rollup, f"rollup missing {needle}"

validation = (ROOT / required[14]).read_text()
for needle in [
    "attributionEnvelopeRetainsSourceRoleWithoutPromotion",
    "manifestationGuardBlocksNearbySourcePromotion",
    "contactProvenanceDoesNotCollapseIntoScientificOrDerivationEvidence",
]:
    assert needle in validation, f"validation missing {needle}"

evidence_validation = (ROOT / required[9]).read_text()
for needle in [
    "externalAndDASHISynthesisRemainDistinct", "primarySecondaryAndDatabaseRolesStayTyped",
    "numericPromotionNeedsExactLocatorAndContext", "unpaidNumericCellsAreNotZeroes",
    "paretoAcquisitionIsNotTruthRanking",
]:
    assert needle in evidence_validation, f"evidence validation missing {needle}"

full = (ROOT / "DASHI/Chemistry/EverythingFull.agda").read_text()
assert "LineageCalibrationDiscriminatorEverything" in full
kit = (ROOT / "DASHI/Biology/KitzerowBH4Everything.agda").read_text()
assert "KitzerowBH4FluxCausalModelsExact" in kit

print("lineage calibration/discriminator + unified attribution/evidence max-cut static contract: PASS")
