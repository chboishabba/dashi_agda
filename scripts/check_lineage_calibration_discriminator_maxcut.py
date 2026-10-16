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
    "DASHI/Chemistry/LineageAcquiredPrimaryEvidenceExact.agda",
    "DASHI/Chemistry/LineageAcquiredQuantitativePaymentsExact.agda",
    "DASHI/Chemistry/LineageEvidenceAcquisitionStatusExact.agda",
    "DASHI/Chemistry/MolecularMechanisticPromotionLadderExact.agda",
    "DASHI/Chemistry/PAHMechanismStatePromotionExact.agda",
    "DASHI/Chemistry/LineageMechanisticPromotionMaxCutValidation.agda",
    "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
    "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
]
for rel in required:
    assert (ROOT / rel).exists(), f"missing {rel}"

for needle in ["chlorAlkaliReplay", "pahReplay", "dhprReplay", "pbCaReplay", "carbonBondReplay"]:
    assert needle in (ROOT / required[0]).read_text(), f"gold replay suite missing {needle}"

source_atlas = (ROOT / required[5]).read_text()
for needle in [
    "AttributedSourceCore", "KitzerowBH4ReactionSourceAtlasExact", "IonicMimicrySourceAtlasExact",
    "chlorAlkaliEuroChlor2022", "dhprBRENDA2026", "astrobiologyPrimer2016",
    "canonicalLineageCalibrationSourceAtlas", "canonicalAtlasNonPromoting",
]:
    assert needle in source_atlas, f"source atlas missing {needle}"
assert "LineageCalibrationAttributionEnvelopeExact" not in source_atlas, "source atlas must not import downstream attribution envelope"

payment = (ROOT / required[6]).read_text()
for needle in [
    "SourceCoordinatePayment", "EvidenceRole", "PaymentGrade",
    "chlorAlkaliTechnicalPayment", "dhprReactionPayment",
    "sourceOwnsDASHISynthesis", "citationCreatesProof",
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

acquired_sources = (ROOT / required[13]).read_text()
for needle in [
    "pahOxygenLineage1985", "pahHumanKinetics1996",
    "pahCatalyticDomainBH4Structure2001", "pahCatalyticDomainBH4PDB1J8U",
    "pahFullLengthBH4Structure2019", "pahFullLengthBH4PDB6HYC",
    "pahQMMPES2004", "pahSingleTurnoverMechanism2013",
    "10.2210/pdb1J8U/pdb", "10.2210/pdb6HYC/pdb", "10.1021/jp048001r", "10.1021/bi301675e",
]:
    assert needle in acquired_sources, f"acquired PAH source atlas missing {needle}"

ladder = (ROOT / required[16]).read_text()
for needle in [
    "PromotionStage", "MolecularMechanisticPromotion", "authorReleasedNumericalArtifact",
    "authorReleasedArtifactEqualsIndependentAuthority", "mechanisticPromotionPaysCausalFlux",
    "deeperMicroscopicModelAlwaysHigherAcquisitionPriority", "consumerSpecificDiscriminatorControlsPriority",
]:
    assert needle in ladder, f"mechanistic promotion ladder missing {needle}"

pah = (ROOT / required[17]).read_text()
for needle in [
    "pah1J8UArtifact", "pah6HYCArtifact", "canonicalPAHMechanisticState",
    "canonicalPAHMechanisticPromotion", "sourceBackedStructurePaid",
    "literalReleasedStructuralCoordinatesPaid", "sourceBackedKineticMechanismPaid",
    "sourceBackedQMMPESPaid", "completeAtomMapPaid", "releasedHamiltonianMatrixPaid",
    "numericRealSpaceWavefunctionPaid", "mechanisticPromotionPaysBH4AllocationFlux",
]:
    assert needle in pah, f"PAH promotion owner missing {needle}"

acquisition = (ROOT / required[12]).read_text()
for needle in [
    "ScientificAcquisitionItem", "ProvenanceAcquisitionItem",
    "bh4FluxDataset", "pahAtomMap", "bh4KineticSet", "chlorLocator",
    "pbCaTargetDataset", "carbonSiliconMatchedDataset", "pahIndependentMechanisticReplay",
    "causalDiscriminatorCanOutrankDeeperMechanisticReplay",
    "stanfordContactArtifact", "brazilCorrespondenceArtifact", "iaccMedMapsContactArtifact",
    "scientificSupportSeparateFromContactProvenance",
    "contactEvidenceAutomaticallyProvesDerivation", "contactEvidenceAutomaticallyProvesPlagiarism",
    "scientificSupportAutomaticallyProvesPriority", "priorityAutomaticallyProvesCorrectness",
    "frontierRankIsTruthRank", "unpaidCoordinateRetainsAttribution", "acquisitionCreatesAuthority",
]:
    assert needle in acquisition, f"unified acquisition frontier missing {needle}"
assert "LineageAttributionAcquisitionParetoExact" not in acquisition, "canonical acquisition frontier must be standalone"

status = (ROOT / required[15]).read_text()
for needle in [
    "pahMechanisticReplayStatus", "mechanisticPromotionClosesFluxTarget",
    "controlled BH4/BH2 + NAD(P)H + J_PAH/J_TH/J_TPH/J_NOS/J_AGMO",
]:
    assert needle in status, f"acquisition status missing {needle}"

rollup = (ROOT / required[19]).read_text()
for needle in [
    "LineageCalibrationAttributionEnvelopeExact", "LineageAttributionEvidenceSourceAtlasExact",
    "LineageAttributionEvidencePaymentExact", "AttributedGoldReactionReplayExact",
    "LineageSourceManifestationGuardExact", "LineageQuantitativeCalibrationLedgerExact",
    "LineageAttributionAcquisitionFrontierExact", "LineageAttributionEvidenceMaxCutValidation",
    "MolecularMechanisticPromotionLadderExact", "PAHMechanismStatePromotionExact",
    "LineageMechanisticPromotionMaxCutValidation",
]:
    assert needle in rollup, f"rollup missing {needle}"
assert "LineageAttributionAcquisitionParetoExact" not in rollup, "rollup must not import deleted parallel frontier"

mechanistic_validation = (ROOT / required[18]).read_text()
for needle in [
    "pahReactionPromotedBeyondStoichiometry", "pahNumericalWavefunctionNotInvented",
    "mechanisticDepthDoesNotSubstituteForFluxDiscriminator", "artifactAndPaperAuthorityRemainDistinct",
]:
    assert needle in mechanistic_validation, f"mechanistic validation missing {needle}"

full = (ROOT / "DASHI/Chemistry/EverythingFull.agda").read_text()
assert "LineageCalibrationDiscriminatorEverything" in full
kit = (ROOT / "DASHI/Biology/KitzerowBH4Everything.agda").read_text()
assert "KitzerowBH4FluxCausalModelsExact" in kit

print("lineage calibration/discriminator + attribution/evidence + mechanistic promotion max-cut static contract: PASS")
