#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

paths = {
    "gold": "DASHI/Chemistry/GoldReactionReplaySuiteExact.agda",
    "bh4": "DASHI/Biology/KitzerowBH4FluxCausalModelsExact.agda",
    "hepatic": "DASHI/Biology/KitzerowBH4HepaticCompetitionDiscriminatorExact.agda",
    "hepatic_v": "DASHI/Biology/KitzerowBH4HepaticCompetitionDiscriminatorValidation.agda",
    "neural_sources": "DASHI/Biology/KitzerowBH4NeuralContextSourceAtlasExact.agda",
    "neural": "DASHI/Biology/KitzerowBH4NeuralContextDiscriminatorExact.agda",
    "neural_v": "DASHI/Biology/KitzerowBH4NeuralContextDiscriminatorValidation.agda",
    "redox": "DASHI/Biology/KitzerowBH4RedoxSpatialDiscriminatorExact.agda",
    "redox_v": "DASHI/Biology/KitzerowBH4RedoxSpatialDiscriminatorValidation.agda",
    "experiment": "DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda",
    "pareto": "DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda",
    "kit_rollup": "DASHI/Biology/KitzerowBH4Everything.agda",
    "acquired_sources": "DASHI/Chemistry/LineageAcquiredPrimaryEvidenceExact.agda",
    "status": "DASHI/Chemistry/LineageEvidenceAcquisitionStatusExact.agda",
    "acquisition": "DASHI/Chemistry/LineageAttributionAcquisitionFrontierExact.agda",
    "chem_rollup": "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
    "chem_validation": "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
    "pah_probe": "DASHI/Chemistry/PAHElectronicStateHamiltonianMonsterProbeExact.agda",
}

for key, rel in paths.items():
    assert (ROOT / rel).exists(), f"missing {key}: {rel}"

text = {k: (ROOT / p).read_text() for k, p in paths.items()}

for needle in ["chlorAlkaliReplay", "pahReplay", "dhprReplay", "pbCaReplay", "carbonBondReplay"]:
    assert needle in text["gold"], f"gold replay suite missing {needle}"

for needle in [
    "numericBranchFluxCalibrated", "competingArchitecturesExplicit",
    "upstreamAllocator", "downstreamConsequence", "parallelRedoxMarker", "contextSpecificSubgroup",
]:
    assert needle in text["bh4"], f"BH4 causal model missing {needle}"

for needle in [
    "sameSystemPAHAndINOSMeasured", "conditionalCompetitionWhenBH4SynthesisBlocked",
    "exogenousBH4RescuesConstrainedSystem", "hepaticTwoBranchResultProvesWholeBH4AllocatorModel",
]:
    assert needle in text["hepatic"], f"hepatic discriminator missing {needle}"

for needle in [
    "sameSystemTwoBranchExperimentIsPaid", "competitionEmergesWhenSupplyIsConstrained",
    "adaptiveSupplyResponseIsObserved", "hepaticResultDoesNotCloseWholeAllocatorModel",
]:
    assert needle in text["hepatic_v"], f"hepatic validation missing {needle}"

for needle in [
    "anastasiadisKuhnLevine1994Uptake", "hylandEtAl1996Hph1",
    "hwangEtAl1998Localization", "liangKaufman1998Striatum",
    "witteveenGiovanelliKaufman1999NOSRedox", "sumiIchinoseEtAl2001PtsKO",
    "choiEtAl2003HumanNnosUptake", "jiangEtAl2024Gch1Therapy",
    "10.1016/0006-8993(94)91154-1", "10.1016/j.neulet.2003.08.032",
    "10.1016/S0006-8993(98)00452-1", "10.1074/jbc.274.42.29755",
    "canonicalNeuralContextAtlasNonPromoting",
]:
    assert needle in text["neural_sources"], f"neural/redox source atlas missing {needle}"

for needle in [
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
    assert needle in text["neural_v"], f"neural validation missing {needle}"

for needle in [
    "BH4PoolNodeKind", "monoamineSynthesisNode", "nNOSSpatialNode", "nosBoundRedoxNode",
    "striatalIntracellularNode", "striatalExtracellularNode", "cellularUptakeNode",
    "humanNnosRecipientNode", "nosReductiveRegenerationEdge", "exogenousBH4UptakeEdge",
    "catecholaminergicToNnosFunctionalCrossTalk", "monoamineToNnosTransferHypothesis",
    "canonicalRedoxSpatialDiscriminator", "nadphRegenerationRelevant",
    "intracellularExtracellularRouteDistinctionPaid", "cellularBH4UptakeDirectlyMeasured",
    "specificMembraneCarrierRequiredByUptakeStudy", "functionalCocultureCrossTalkSupported",
    "scalarWellMixedPoolSufficient", "intercellBH4TransferDirectlyMeasured",
    "redoxSpatialEvidenceClosesWholeAllocator",
    "TopologyResolvedPoolBalance", "canonicalTopologyResolvedPoolBalance",
    "topologyResolvedStateRequired", "scalarProjectionIsLossy",
    "numericEdgeFluxesPaid", "directTransferFluxPaid",
]:
    assert needle in text["redox"], f"redox/spatial discriminator missing {needle}"

for needle in [
    "redoxRegenerationAndSpatialTopologyArePaidWithoutScalarPoolPromotion",
    "cellularUptakeAndFunctionalCrossTalkArePaidWithoutInventingFlux",
    "neuralSupplyAndConsumptionNeedNotBeColocalized",
    "striatalRouteAmbiguityBlocksNaiveCofactorInterpretation",
    "topologyResolvedBalanceReplacesScalarAsSufficientStateWithoutInventingFlux",
    "redoxSpatialEvidenceDoesNotCloseWholeAllocator",
]:
    assert needle in text["redox_v"], f"redox/spatial validation missing {needle}"

for needle in [
    "historicalSameObjectConstraint", "historicalNeuralContextConstraint",
    "historicalRedoxSpatialConstraint", "historicalRedoxSpatialConstraintPaid",
    "NOS-bound BH4 redox/coupling", "intracellular versus extracellular route",
    "remainingExperimentalResidual", "historicalConstraintsCloseCentralEdge",
]:
    assert needle in text["experiment"], f"BH4 experiment owner missing {needle}"

for needle in [
    "target-relevant route-resolved multi-branch BH4 allocation experiment",
    "NOS-bound BH4 redox/coupling", "historicalDirectDiscriminatorChangesTargetDefinition",
    "historicalDirectDiscriminatorClosesWholeTarget",
]:
    assert needle in text["pareto"], f"BH4 Pareto owner missing {needle}"

for needle in [
    "pahFerrylIntermediate2011", "bh4HepaticCompetition1996",
    "10.1021/bi1019868", "10.1074/jbc.271.40.24534",
]:
    assert needle in text["acquired_sources"], f"acquired source atlas missing {needle}"

for needle in [
    "bh4FluxStatus", "bh4NeuralContextStatus", "bh4RedoxSpatialStatus",
    "partiallyPaid", "paidForDeclaredCoordinate", "scalarWellMixedPoolSufficient",
    "directIntercellularTransferAlreadyPaid", "directDiscriminatorCanUpgradePreviouslyUnpaidTargetToPartial",
    "quantitative donor-to-recipient transfer flux",
]:
    assert needle in text["status"], f"acquisition status missing {needle}"

for needle in [
    "A1 target-relevant route/compartment-resolved multi-branch BH4 allocation discriminator beyond paid hepatic/neural/redox-spatial constraints",
    "NOS-bound BH4 redox/coupling", "intracellular/extracellular route", "transfer/supply topology",
    "frontierRankIsTruthRank", "unpaidCoordinateRetainsAttribution", "acquisitionCreatesAuthority",
]:
    assert needle in text["acquisition"], f"global acquisition frontier missing {needle}"

for needle in [
    "KitzerowBH4HepaticCompetitionDiscriminatorExact",
    "KitzerowBH4NeuralContextSourceAtlasExact", "KitzerowBH4NeuralContextDiscriminatorExact",
    "KitzerowBH4RedoxSpatialDiscriminatorExact", "KitzerowBH4RedoxSpatialDiscriminatorValidation",
]:
    assert needle in text["kit_rollup"], f"Kitzerow rollup missing {needle}"
    assert needle in text["chem_rollup"], f"chemistry rollup missing {needle}"

for needle in [
    "bh4DirectDiscriminatorsPaySubcoordinatesWithoutWholeClosure",
    "bh4RedoxSpatialCoordinateIsPaidWithoutInventingTransfer",
    "bh4TransportEvidenceDoesNotRequireDedicatedCarrierOrQuantifyInVivoFlux",
    "bh4TopologyResolvedBalanceRetainsNumericalAcquisitionDebt",
    "bh4AcquisitionStateIsPartialNotClosed",
]:
    assert needle in text["chem_validation"], f"chemistry validation missing {needle}"

for needle in [
    "canonicalPAHFiniteHamiltonianProbe", "sourceBackedNumericalHamiltonianMatrixPaid",
    "canonicalPAHMonster3BProbe", "sameObjectC3CoordinatePaid", "nontrivialMonsterActionOnPAHStatePaid",
]:
    assert needle in text["pah_probe"], f"PAH Hamiltonian/Monster boundary missing {needle}"

full = (ROOT / "DASHI/Chemistry/EverythingFull.agda").read_text()
assert "LineageCalibrationDiscriminatorEverything" in full

print("lineage/BH4 causal acquisition + topology-resolved redox/spatial/transport + attribution/mechanistic max-cut static contract: PASS")
