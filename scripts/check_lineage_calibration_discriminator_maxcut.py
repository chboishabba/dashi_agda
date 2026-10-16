#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

paths = {
    "gold": "DASHI/Chemistry/GoldReactionReplaySuiteExact.agda",
    "pbca": "DASHI/Biology/LeadCalciumEndToEndReplayExact.agda",
    "bh4": "DASHI/Biology/KitzerowBH4FluxCausalModelsExact.agda",
    "bidi": "DASHI/Chemistry/LineageBidiDiscriminatorSynthesisExact.agda",
    "carbon": "DASHI/Biology/CarbonSiliconReachableChemistryBenchmarkExact.agda",
    "atlas": "DASHI/Chemistry/LineageAttributionEvidenceSourceAtlasExact.agda",
    "payment": "DASHI/Chemistry/LineageAttributionEvidencePaymentExact.agda",
    "replay": "DASHI/Chemistry/AttributedGoldReactionReplayExact.agda",
    "numeric": "DASHI/Chemistry/LineageQuantitativeCalibrationLedgerExact.agda",
    "evidence_validation": "DASHI/Chemistry/LineageAttributionEvidenceMaxCutValidation.agda",
    "attribution": "DASHI/Chemistry/LineageCalibrationAttributionEnvelopeExact.agda",
    "manifestation": "DASHI/Chemistry/LineageSourceManifestationGuardExact.agda",
    "acquisition": "DASHI/Chemistry/LineageAttributionAcquisitionFrontierExact.agda",
    "acquired_sources": "DASHI/Chemistry/LineageAcquiredPrimaryEvidenceExact.agda",
    "acquired_payments": "DASHI/Chemistry/LineageAcquiredQuantitativePaymentsExact.agda",
    "status": "DASHI/Chemistry/LineageEvidenceAcquisitionStatusExact.agda",
    "ladder": "DASHI/Chemistry/MolecularMechanisticPromotionLadderExact.agda",
    "pah": "DASHI/Chemistry/PAHMechanismStatePromotionExact.agda",
    "mechanistic_validation": "DASHI/Chemistry/LineageMechanisticPromotionMaxCutValidation.agda",
    "electronic_probe": "DASHI/Chemistry/PAHElectronicStateHamiltonianMonsterProbeExact.agda",
    "electronic_validation": "DASHI/Chemistry/PAHElectronicStateHamiltonianMonsterProbeValidation.agda",
    "rollup": "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
    "validation": "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
}

for key, rel in paths.items():
    assert (ROOT / rel).exists(), f"missing {key}: {rel}"

text = {k: (ROOT / p).read_text() for k, p in paths.items()}

for needle in ["chlorAlkaliReplay", "pahReplay", "dhprReplay", "pbCaReplay", "carbonBondReplay"]:
    assert needle in text["gold"], f"gold replay suite missing {needle}"

for needle in [
    "chlorAlkaliEuroChlor2022", "dhprBRENDA2026", "astrobiologyPrimer2016",
    "canonicalLineageCalibrationSourceAtlas", "canonicalAtlasNonPromoting",
]:
    assert needle in text["atlas"], f"source atlas missing {needle}"
assert "LineageCalibrationAttributionEnvelopeExact" not in text["atlas"], "source atlas must not import downstream attribution envelope"

for needle in [
    "SourceCoordinatePayment", "EvidenceRole", "PaymentGrade", "chlorAlkaliTechnicalPayment",
    "dhprReactionPayment", "sourceOwnsDASHISynthesis", "citationCreatesProof",
    "citationAlonePaysCalibration", "missingCoordinatePromotedByNearbyCitation",
    "reviewCountsAsPrimaryExperimentByDefault", "databaseReactionIdentityCountsAsInVivoFlux",
    "exactLocatorRequiredForNumericPromotion",
]:
    assert needle in text["payment"], f"evidence payment owner missing {needle}"

for needle in [
    "AttributedGoldReplay", "canonicalAttributedGoldReplays", "sourceOwnsReplayComposition",
    "replayCompositionErasesSourceIdentity", "unpaidCoordinatesRemainAttributed",
    "dashiAndExternalOwnershipRemainDistinct",
]:
    assert needle in text["replay"], f"attributed replay owner missing {needle}"

for needle in [
    "QuantitativeCalibrationCell", "bh4BranchFluxCell", "pahKineticCell", "chlorElectrodeCell",
    "pbCaAffinityCell", "carbonSiliconYieldCell", "numberWithoutExactLocatorPromoted",
    "numberWithoutContextPromoted", "unpaidCoordinateInterpretedAsZero",
    "exactUnitsAndUncertaintyRemainRequired",
]:
    assert needle in text["numeric"], f"quantitative calibration ledger missing {needle}"

for needle in [
    "pahOxygenLineage1985", "pahHumanKinetics1996", "pahCatalyticDomainBH4Structure2001",
    "pahCatalyticDomainBH4PDB1J8U", "pahFullLengthBH4Structure2019",
    "pahFullLengthBH4PDB6HYC", "pahQMMPES2004", "pahSingleTurnoverMechanism2013",
    "10.2210/pdb1J8U/pdb", "10.2210/pdb6HYC/pdb", "10.1021/jp048001r", "10.1021/bi301675e",
]:
    assert needle in text["acquired_sources"], f"acquired PAH source atlas missing {needle}"

for needle in [
    "PromotionStage", "MolecularMechanisticPromotion", "authorReleasedNumericalArtifact",
    "authorReleasedArtifactEqualsIndependentAuthority", "mechanisticPromotionPaysCausalFlux",
    "deeperMicroscopicModelAlwaysHigherAcquisitionPriority", "consumerSpecificDiscriminatorControlsPriority",
]:
    assert needle in text["ladder"], f"mechanistic promotion ladder missing {needle}"

for needle in [
    "pah1J8UArtifact", "pah6HYCArtifact", "canonicalPAHMechanisticState",
    "canonicalPAHMechanisticPromotion", "sourceBackedStructurePaid",
    "literalReleasedStructuralCoordinatesPaid", "sourceBackedKineticMechanismPaid",
    "sourceBackedQMMPESPaid", "completeAtomMapPaid", "releasedHamiltonianMatrixPaid",
    "numericRealSpaceWavefunctionPaid", "mechanisticPromotionPaysBH4AllocationFlux",
]:
    assert needle in text["pah"], f"PAH promotion owner missing {needle}"

for needle in [
    "panayEtAl2011Ferryl", "PAHCatalyticElectronicState", "bacterialFerrylReceipt",
    "canonicalPAHFiniteHamiltonianProbe", "sourceBackedNumericalHamiltonianMatrixPaid",
    "numericalDiagonalizationPaid", "eigenvectorCoefficientsPaid",
    "canonicalPAHMonster3BProbe", "observedAssemblySymmetry", "sameObjectC3CoordinatePaid",
    "canonicalD2ToMonsterC3IntertwinerPaid", "nontrivialMonsterActionOnPAHStatePaid",
    "trivialActionCountsAsPhysicalMonsterEvidence", "canonicalPAHElectronicMonsterBoundary",
    "microscopicPromotionPaysBH4AllocationFlux",
]:
    assert needle in text["electronic_probe"], f"PAH electronic/Monster probe missing {needle}"

for needle in [
    "literalStateCarrierWithoutFabricatedHamiltonian",
    "bacterialFerrylDoesNotBecomeHumanSameObjectByAnalogy",
    "finiteOperatorTypeDoesNotCreateMatrixOrEigenvector",
    "pahD2DoesNotManufactureMonsterC3",
    "trivialActionIsExplicitlyNonDiagnostic",
    "microscopicDepthStillDoesNotPayAllocation",
]:
    assert needle in text["electronic_validation"], f"PAH electronic validation missing {needle}"

for needle in [
    "bh4FluxDataset", "pahAtomMap", "bh4KineticSet", "chlorLocator",
    "pbCaTargetDataset", "carbonSiliconMatchedDataset", "pahIndependentMechanisticReplay",
    "causalDiscriminatorCanOutrankDeeperMechanisticReplay",
    "stanfordContactArtifact", "brazilCorrespondenceArtifact", "iaccMedMapsContactArtifact",
    "scientificSupportSeparateFromContactProvenance", "contactEvidenceAutomaticallyProvesDerivation",
    "contactEvidenceAutomaticallyProvesPlagiarism", "scientificSupportAutomaticallyProvesPriority",
    "priorityAutomaticallyProvesCorrectness", "frontierRankIsTruthRank",
    "unpaidCoordinateRetainsAttribution", "acquisitionCreatesAuthority",
]:
    assert needle in text["acquisition"], f"unified acquisition frontier missing {needle}"
assert "LineageAttributionAcquisitionParetoExact" not in text["acquisition"], "canonical acquisition frontier must be standalone"

for needle in [
    "pahMechanisticReplayStatus", "pahElectronicHamiltonianMonsterStatus",
    "mechanisticPromotionClosesFluxTarget", "failedMonsterProbeCreatesAcquisitionPriority",
    "controlled BH4/BH2 + NAD(P)H + J_PAH/J_TH/J_TPH/J_NOS/J_AGMO",
]:
    assert needle in text["status"], f"acquisition status missing {needle}"

for needle in [
    "MolecularMechanisticPromotionLadderExact", "PAHMechanismStatePromotionExact",
    "LineageMechanisticPromotionMaxCutValidation", "PAHElectronicStateHamiltonianMonsterProbeExact",
    "PAHElectronicStateHamiltonianMonsterProbeValidation", "LineageAttributionAcquisitionFrontierExact",
]:
    assert needle in text["rollup"], f"rollup missing {needle}"
assert "LineageAttributionAcquisitionParetoExact" not in text["rollup"], "rollup must not import deleted parallel frontier"

for needle in [
    "pahReactionPromotedBeyondStoichiometry", "pahNumericalWavefunctionNotInvented",
    "mechanisticDepthDoesNotSubstituteForFluxDiscriminator", "artifactAndPaperAuthorityRemainDistinct",
]:
    assert needle in text["mechanistic_validation"], f"mechanistic validation missing {needle}"

for needle in [
    "externalAndDASHISynthesisRemainDistinct", "primarySecondaryAndDatabaseRolesStayTyped",
    "numericPromotionNeedsExactLocatorAndContext", "unpaidNumericCellsAreNotZeroes",
    "paretoAcquisitionIsNotTruthRanking",
]:
    assert needle in text["evidence_validation"], f"evidence validation missing {needle}"

full = (ROOT / "DASHI/Chemistry/EverythingFull.agda").read_text()
assert "LineageCalibrationDiscriminatorEverything" in full
kit = (ROOT / "DASHI/Biology/KitzerowBH4Everything.agda").read_text()
assert "KitzerowBH4FluxCausalModelsExact" in kit

print("lineage calibration/discriminator + attribution/evidence + mechanistic/electronic promotion max-cut static contract: PASS")
