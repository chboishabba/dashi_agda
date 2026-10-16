#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

paths = {
    "gold": "DASHI/Chemistry/GoldReactionReplaySuiteExact.agda",
    "pbca": "DASHI/Biology/LeadCalciumEndToEndReplayExact.agda",
    "bh4": "DASHI/Biology/KitzerowBH4FluxCausalModelsExact.agda",
    "hepatic": "DASHI/Biology/KitzerowBH4HepaticCompetitionDiscriminatorExact.agda",
    "hepatic_validation": "DASHI/Biology/KitzerowBH4HepaticCompetitionDiscriminatorValidation.agda",
    "neural_sources": "DASHI/Biology/KitzerowBH4NeuralContextSourceAtlasExact.agda",
    "neural": "DASHI/Biology/KitzerowBH4NeuralContextDiscriminatorExact.agda",
    "neural_validation": "DASHI/Biology/KitzerowBH4NeuralContextDiscriminatorValidation.agda",
    "redox_spatial": "DASHI/Biology/KitzerowBH4RedoxSpatialDiscriminatorExact.agda",
    "redox_spatial_validation": "DASHI/Biology/KitzerowBH4RedoxSpatialDiscriminatorValidation.agda",
    "bh4_experiment": "DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda",
    "bh4_pareto": "DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda",
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
assert "LineageCalibrationAttributionEnvelopeExact" not in text["atlas"]

for needle in [
    "pahFerrylIntermediate2011", "bh4HepaticCompetition1996",
    "10.1021/bi1019868", "10.1074/jbc.271.40.24534",
    "pahCatalyticDomainBH4PDB1J8U", "pahFullLengthBH4PDB6HYC",
    "pahQMMPES2004", "pahSingleTurnoverMechanism2013",
]:
    assert needle in text["acquired_sources"], f"acquired source atlas missing {needle}"

for needle in [
    "hylandEtAl1996Hph1", "hwangEtAl1998Localization", "liangKaufman1998Striatum",
    "witteveenGiovanelliKaufman1999NOSRedox", "sumiIchinoseEtAl2001PtsKO",
    "jiangEtAl2024Gch1Therapy", "10.1002/(SICI)1098-2396(199802)28:2<140::AID-SYN4>3.0.CO;2-B",
    "10.1016/S0006-8993(98)00452-1", "10.1074/jbc.274.42.29755",
    "canonicalNeuralContextAtlasNonPromoting",
]:
    assert needle in text["neural_sources"], f"neural/redox source atlas missing {needle}"

for needle in [
    "basalOutput", "pheOutput", "dahpOutput", "pheDahpOutput", "pheBh4DahpOutput",
    "2373 +/- 90", "2493 +/- 303", "1069 +/- 228", "3536 +/- 545",
    "basalPterin", "phePterin", "dahpPterin", "pheDahpPterin",
    "19.2 +/- 1.4", "17.0 +/- 0.7", "1.8 +/- 0.1", "1.0 +/- 0.4",
    "sameSystemPAHAndINOSMeasured", "conditionalCompetitionWhenBH4SynthesisBlocked",
    "exogenousBH4RescuesConstrainedSystem", "hepaticTwoBranchResultProvesWholeBH4AllocatorModel",
]:
    assert needle in text["hepatic"], f"hepatic discriminator missing {needle}"

for needle in [
    "sameSystemTwoBranchExperimentIsPaid",
    "strongFixedPoolCompetitionIsNotSupportedInThisHepaticContext",
    "competitionEmergesWhenSupplyIsConstrained", "adaptiveSupplyResponseIsObserved",
    "hepaticResultDoesNotCloseWholeAllocatorModel",
]:
    assert needle in text["hepatic_validation"], f"hepatic validation missing {needle}"

for needle in [
    "hph1Observation", "ptsKOObservation", "jiang2024Observation",
    "brainBH4RestoredWithoutMonoamineRescue", "brainBH4RestoredWithoutDopamineRescue",
    "enzymeAbundanceStateMatters", "brainRegionContextMatters", "developmentalTimingMatters",
    "simpleCurrentPoolSufficiencySupported", "contextSpecificArchitectureSupportedAsLiveAlternative",
]:
    assert needle in text["neural"], f"neural discriminator missing {needle}"

for needle in [
    "poolRestorationDoesNotGuaranteeFunctionalRescue",
    "stateHistoryAndRegionRemainCausalCoordinates",
    "neuralEvidenceConstrainsSimpleAllocatorWithoutClosingWholeModel",
]:
    assert needle in text["neural_validation"], f"neural validation missing {needle}"

for needle in [
    "BH4PoolNodeKind", "monoamineSynthesisNode", "nNOSSpatialNode", "nosBoundRedoxNode",
    "striatalIntracellularNode", "striatalExtracellularNode", "nosReductiveRegenerationEdge",
    "monoamineToNnosTransferHypothesis", "intracellularBH4ToDopamineRelease",
    "extracellularBH4ToDopamineRelease", "canonicalRedoxSpatialDiscriminator",
    "nadphRegenerationRelevant", "intracellularExtracellularRouteDistinctionPaid",
    "scalarWellMixedPoolSufficient", "intercellBH4TransferDirectlyMeasured",
    "exogenousBH4EffectRequiresTHOrNOS", "redoxSpatialEvidenceClosesWholeAllocator",
]:
    assert needle in text["redox_spatial"], f"redox/spatial discriminator missing {needle}"

for needle in [
    "redoxRegenerationAndSpatialTopologyArePaidWithoutScalarPoolPromotion",
    "neuralSupplyAndConsumptionNeedNotBeColocalized",
    "striatalRouteAmbiguityBlocksNaiveCofactorInterpretation",
    "redoxSpatialEvidenceDoesNotCloseWholeAllocator",
]:
    assert needle in text["redox_spatial_validation"], f"redox/spatial validation missing {needle}"

for needle in [
    "historicalSameObjectConstraint", "historicalNeuralContextConstraint",
    "historicalRedoxSpatialConstraint", "historicalTwoBranchConstraintPaid",
    "historicalNeuralContextConstraintPaid", "historicalRedoxSpatialConstraintPaid",
    "historicalConstraintsCloseCentralEdge", "remainingExperimentalResidual",
    "intracellular versus extracellular route", "NOS-bound BH4 redox/coupling",
]:
    assert needle in text["bh4_experiment"], f"BH4 experiment owner missing {needle}"

for needle in [
    "historicalDirectDiscriminatorChangesTargetDefinition",
    "historicalDirectDiscriminatorClosesWholeTarget",
    "route-resolved multi-branch BH4 allocation experiment",
    "NOS-bound BH4 redox/coupling",
]:
    assert needle in text["bh4_pareto"], f"BH4 pareto owner missing {needle}"

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
    "PAHCatalyticElectronicState", "bacterialFerrylReceipt",
    "LineageAcquiredPrimaryEvidenceExact.pahFerrylIntermediate2011",
    "canonicalPAHFiniteHamiltonianProbe", "sourceBackedNumericalHamiltonianMatrixPaid",
    "numericalDiagonalizationPaid", "eigenvectorCoefficientsPaid",
    "canonicalPAHMonster3BProbe", "observedAssemblySymmetry", "sameObjectC3CoordinatePaid",
    "canonicalD2ToMonsterC3IntertwinerPaid", "nontrivialMonsterActionOnPAHStatePaid",
    "trivialActionCountsAsPhysicalMonsterEvidence", "canonicalPAHElectronicMonsterBoundary",
    "microscopicPromotionPaysBH4AllocationFlux",
]:
    assert needle in text["electronic_probe"], f"PAH electronic/Monster probe missing {needle}"
assert "panayEtAl2011Ferryl" not in text["electronic_probe"], "ferryl source identity must stay canonical in acquired source atlas"

for needle in [
    "literalStateCarrierWithoutFabricatedHamiltonian",
    "bacterialFerrylDoesNotBecomeHumanSameObjectByAnalogy",
    "finiteOperatorTypeDoesNotCreateMatrixOrEigenvector",
    "pahD2DoesNotManufactureMonsterC3", "trivialActionIsExplicitlyNonDiagnostic",
    "microscopicDepthStillDoesNotPayAllocation",
]:
    assert needle in text["electronic_validation"], f"PAH electronic validation missing {needle}"

for needle in [
    "A1 target-relevant route/compartment-resolved multi-branch BH4 allocation discriminator beyond paid hepatic/neural/redox-spatial constraints",
    "NOS-bound BH4 redox/coupling", "intracellular/extracellular route", "transfer/supply topology",
    "pahIndependentMechanisticReplay", "causalDiscriminatorCanOutrankDeeperMechanisticReplay",
    "stanfordContactArtifact", "brazilCorrespondenceArtifact", "iaccMedMapsContactArtifact",
    "scientificSupportSeparateFromContactProvenance", "contactEvidenceAutomaticallyProvesDerivation",
    "contactEvidenceAutomaticallyProvesPlagiarism", "scientificSupportAutomaticallyProvesPriority",
    "priorityAutomaticallyProvesCorrectness", "frontierRankIsTruthRank",
    "unpaidCoordinateRetainsAttribution", "acquisitionCreatesAuthority",
]:
    assert needle in text["acquisition"], f"unified acquisition frontier missing {needle}"
assert "LineageAttributionAcquisitionParetoExact" not in text["acquisition"]

for needle in [
    "bh4FluxStatus", "partiallyPaid", "bh4NeuralContextStatus", "bh4RedoxSpatialStatus",
    "paidForDeclaredCoordinate", "hepaticTwoBranchPaymentClosesWholeMultiBranchTarget",
    "currentPoolRestorationGuaranteesFunctionalRescue", "scalarWellMixedPoolSufficient",
    "directIntercellularTransferAlreadyPaid", "directDiscriminatorCanUpgradePreviouslyUnpaidTargetToPartial",
    "pahMechanisticReplayStatus", "pahElectronicHamiltonianMonsterStatus",
    "mechanisticPromotionClosesFluxTarget", "failedMonsterProbeCreatesAcquisitionPriority",
]:
    assert needle in text["status"], f"acquisition status missing {needle}"

for needle in [
    "KitzerowBH4HepaticCompetitionDiscriminatorExact",
    "KitzerowBH4NeuralContextSourceAtlasExact", "KitzerowBH4NeuralContextDiscriminatorExact",
    "KitzerowBH4RedoxSpatialDiscriminatorExact", "KitzerowBH4RedoxSpatialDiscriminatorValidation",
    "MolecularMechanisticPromotionLadderExact", "PAHMechanismStatePromotionExact",
    "LineageMechanisticPromotionMaxCutValidation", "PAHElectronicStateHamiltonianMonsterProbeExact",
    "PAHElectronicStateHamiltonianMonsterProbeValidation", "LineageAttributionAcquisitionFrontierExact",
]:
    assert needle in text["rollup"], f"rollup missing {needle}"

for needle in [
    "bh4DirectDiscriminatorsPaySubcoordinatesWithoutWholeClosure",
    "bh4RedoxSpatialCoordinateIsPaidWithoutInventingTransfer",
    "bh4AcquisitionStateIsPartialNotClosed",
    "contactDoesNotProvePlagiarism", "scientificSupportDoesNotProvePriority",
    "priorityDoesNotProveCorrectness",
]:
    assert needle in text["validation"], f"chemistry validation missing {needle}"

for needle in [
    "externalAndDASHISynthesisRemainDistinct", "primarySecondaryAndDatabaseRolesStayTyped",
    "numericPromotionNeedsExactLocatorAndContext", "unpaidNumericCellsAreNotZeroes",
    "paretoAcquisitionIsNotTruthRanking",
]:
    assert needle in text["evidence_validation"], f"evidence validation missing {needle}"

full = (ROOT / "DASHI/Chemistry/EverythingFull.agda").read_text()
assert "LineageCalibrationDiscriminatorEverything" in full
kit = (ROOT / "DASHI/Biology/KitzerowBH4Everything.agda").read_text()
for needle in [
    "KitzerowBH4FluxCausalModelsExact", "KitzerowBH4HepaticCompetitionDiscriminatorExact",
    "KitzerowBH4NeuralContextSourceAtlasExact", "KitzerowBH4NeuralContextDiscriminatorExact",
    "KitzerowBH4RedoxSpatialDiscriminatorExact", "KitzerowBH4RedoxSpatialDiscriminatorValidation",
]:
    assert needle in kit, f"Kitzerow BH4 rollup missing {needle}"

print("lineage/BH4 causal acquisition + redox/spatial topology + attribution + mechanistic/electronic promotion max-cut static contract: PASS")
