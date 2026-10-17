module DASHI.Biology.BH4Phase4SystemStateRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Executed
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Biology.BH4CompartmentKineticStateExact as Parameters
import DASHI.Biology.BH4QuantitativeAcquisitionExact as Acquisition
import DASHI.Biology.BH4ExecutedSABIOReceiptExact as SABIO
import DASHI.Biology.BH4ExecutedSIFTSReceiptExact as SIFTS
import DASHI.Biology.BH4IntervalFluxSolverExact as Interval
import DASHI.Biology.BH4NOSCouplingEvidenceExact as Evidence
import DASHI.Biology.BH4NOSCouplingSameObjectExact as NOS
import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.BH4OpenMetabolicNetworkAdapterExact as OpenNetwork
import DASHI.Biology.BH4Phase4RoadmapExact as Roadmap
import DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact as Graph

panelReactionAcquisitionExecuted :
  Executed.acquisitionExecuted Executed.canonicalExecutedPanelReactionReceipt ≡ true
panelReactionAcquisitionExecuted = refl

executedPanelHasTwelveFiniteReactions : Matrix.executedPanelReactionCount ≡ 12
executedPanelHasTwelveFiniteReactions = refl

executedPanelHasTwentyNineFiniteSpecies : Matrix.executedPanelSpeciesCount ≡ 29
executedPanelHasTwentyNineFiniteSpecies = refl

matrixDoesNotInventMissingChemistry :
  Matrix.BH4PanelMatrixBoundary.formulaIncompleteReactionBecomesZeroColumn
    Matrix.canonicalBH4PanelMatrixBoundary
  ≡ false
matrixDoesNotInventMissingChemistry = refl

unresolvedParameterIsNotZeroMeasurement :
  Parameters.BH4ParameterBoundary.unresolvedParameterMayBeReadAsMeasuredZero
    Parameters.canonicalBH4ParameterBoundary
  ≡ false
unresolvedParameterIsNotZeroMeasurement = refl

compartmentIdentityCannotBeDropped :
  Parameters.BH4ParameterBoundary.sameMoleculeDifferentCompartmentMayBeCollapsed
    Parameters.canonicalBH4ParameterBoundary
  ≡ false
compartmentIdentityCannotBeDropped = refl

sabioKineticConstantDoesNotBecomeFluxBound :
  Acquisition.QuantitativeAcquisitionBoundary.kineticConstantCreatesFluxBound
    Acquisition.canonicalQuantitativeAcquisitionBoundary
  ≡ false
sabioKineticConstantDoesNotBecomeFluxBound = refl

executedSABIOExportRecoveredOneHundredNinetyRows :
  SABIO.executedSABIOKineticEntryCount ≡ 190
executedSABIOExportRecoveredOneHundredNinetyRows = refl

executedSABIOExportCoveredElevenProteins :
  SABIO.executedSABIOProteinsWithEntries ≡ 11
executedSABIOExportCoveredElevenProteins = refl

executedSABIOExportHadZeroAcquisitionErrors :
  SABIO.executedSABIOAcquisitionErrorCount ≡ 0
executedSABIOExportHadZeroAcquisitionErrors = refl

preRepairZeroParameterCountIsNotScientificZero :
  SABIO.ExecutedSABIOBoundary.zeroPreRepairParameterCountMeansNoKineticParameters
    SABIO.canonicalExecutedSABIOBoundary
  ≡ false
preRepairZeroParameterCountIsNotScientificZero = refl

sabioExportRowsStillDoNotPayFluxBounds :
  SABIO.ExecutedSABIOBoundary.exportRowCreatesInVivoFluxBound
    SABIO.canonicalExecutedSABIOBoundary
  ≡ false
sabioExportRowsStillDoNotPayFluxBounds = refl

siftsMappingDoesNotCreateCatalyticMechanism :
  Acquisition.QuantitativeAcquisitionBoundary.structureMappingCreatesCatalyticMechanism
    Acquisition.canonicalQuantitativeAcquisitionBoundary
  ≡ false
siftsMappingDoesNotCreateCatalyticMechanism = refl

boundedSIFTSRunExaminedThirtyEightStructures :
  SIFTS.structuresExamined SIFTS.canonicalExecutedSIFTSReceipt ≡ 38
boundedSIFTSRunExaminedThirtyEightStructures = refl

boundedSIFTSRunRecoveredFiveHundredTwentySixSegments :
  SIFTS.matchingSIFTSSegmentCount SIFTS.canonicalExecutedSIFTSReceipt ≡ 526
boundedSIFTSRunRecoveredFiveHundredTwentySixSegments = refl

boundedSIFTSMappingStillDoesNotCreateCatalyticFunction :
  SIFTS.ExecutedSIFTSBoundary.mappingCreatesCatalyticFunction
    SIFTS.canonicalExecutedSIFTSBoundary
  ≡ false
boundedSIFTSMappingStillDoesNotCreateCatalyticFunction = refl

intervalSolverDoesNotZeroMissingExchange :
  Interval.IntervalFluxSolverBoundary.missingExchangeBoundMayBeSubstitutedWithZero
    Interval.canonicalIntervalFluxSolverBoundary
  ≡ false
intervalSolverDoesNotZeroMissingExchange = refl

intervalSteadyStateDoesNotProveDiseaseMechanism :
  Interval.IntervalFluxSolverBoundary.feasibleSteadyStateCreatesDiseaseMechanism
    Interval.canonicalIntervalFluxSolverBoundary
  ≡ false
intervalSteadyStateDoesNotProveDiseaseMechanism = refl

nosReactionChemistryIsNowPaid :
  Graph.reactionOrRelationPaid Graph.bh4ToNOSCouplingEdge ≡ true
nosReactionChemistryIsNowPaid = refl

aaahReactionChemistryIsNowPaid :
  Graph.reactionOrRelationPaid Graph.aaahCompetitionEdge ≡ true
aaahReactionChemistryIsNowPaid = refl

agmoReactionChemistryIsNowPaid :
  Graph.reactionOrRelationPaid Graph.agmoCompetitionEdge ≡ true
agmoReactionChemistryIsNowPaid = refl

nosProteinPresenceDoesNotPayCouplingTransition :
  NOS.BH4NOSSameObjectBoundary.proteinPresencePaysCouplingTransition
    NOS.canonicalBH4NOSSameObjectBoundary
  ≡ false
nosProteinPresenceDoesNotPayCouplingTransition = refl

noAndN2oRemainDistinctAcrossSameObjectBridge :
  NOS.BH4NOSSameObjectBoundary.nitrousOxideMayStandForNitricOxideProduct
    NOS.canonicalBH4NOSSameObjectBoundary
  ≡ false
noAndN2oRemainDistinctAcrossSameObjectBridge = refl

nos3EvidenceDoesNotGlobalizeToNOS1 :
  Evidence.NOS3EvidenceBoundary.nos3EvidenceGlobalizesToNOS1
    Evidence.canonicalNOS3EvidenceBoundary
  ≡ false
nos3EvidenceDoesNotGlobalizeToNOS1 = refl

nos3ExperimentalSystemDoesNotBecomeSameSingleCell :
  NOS.BH4NOSSameObjectBoundary.nos3ExperimentalSystemEvidencePaysSameSingleCellState
    NOS.canonicalBH4NOSSameObjectBoundary
  ≡ false
nos3ExperimentalSystemDoesNotBecomeSameSingleCell = refl

missingBoundsProduceUnderdeterminedNotZeroFlux :
  Flux.BH4FluxFeasibilityBoundary.missingFluxBoundMayBeSubstitutedWithZero
    Flux.canonicalBH4FluxFeasibilityBoundary
  ≡ false
missingBoundsProduceUnderdeterminedNotZeroFlux = refl

feasibleFluxDoesNotProveDiseaseMechanism :
  Flux.BH4FluxFeasibilityBoundary.feasibleFluxStateProvesDiseaseMechanism
    Flux.canonicalBH4FluxFeasibilityBoundary
  ≡ false
feasibleFluxDoesNotProveDiseaseMechanism = refl

exchangeIsNotInternalReaction :
  OpenNetwork.BH4OpenMetabolicBoundary.externalExchangeMayBeCollapsedIntoInternalStoichiometry
    OpenNetwork.canonicalBH4OpenMetabolicBoundary
  ≡ false
exchangeIsNotInternalReaction = refl

wholeSystemFluxAttemptHasOccurred : Roadmap.wholeSystemFluxBalanceAttempted ≡ true
wholeSystemFluxAttemptHasOccurred = refl

firstWholeSystemFluxOutcomeIsUnderdetermined :
  Roadmap.firstJointFluxOutcome ≡ Flux.underdetermined
firstWholeSystemFluxOutcomeIsUnderdetermined = refl

firstAttemptMissingTwelveFluxBounds : Roadmap.missingReactionFluxBounds ≡ 12
firstAttemptMissingTwelveFluxBounds = refl

firstAttemptMissingTwelveFluxValues : Roadmap.missingReactionFluxValues ≡ 12
firstAttemptMissingTwelveFluxValues = refl

firstAttemptMissingTwentyNineExchangeCoordinates :
  Roadmap.missingExternalExchangeCoordinates ≡ 29
firstAttemptMissingTwentyNineExchangeCoordinates = refl

historicalFirstTemplateHasTwentySevenCoordinates :
  Roadmap.firstQuantitativeCoordinateCount ≡ 27
historicalFirstTemplateHasTwentySevenCoordinates = refl

nextTemplateHasFiftySixCoordinates :
  Roadmap.expandedQuantitativeCoordinateCount ≡ 56
nextTemplateHasFiftySixCoordinates = refl

quantitativeAcquisitionAndIntervalSolverAreReady :
  Roadmap.quantitativeAcquisitionToolingReady ≡ true
  × Roadmap.intervalFluxSolverReady ≡ true
quantitativeAcquisitionAndIntervalSolverAreReady = refl , refl

sabioExportAPIAdapterIsReady : Roadmap.sabioExportAPIAdapterReady ≡ true
sabioExportAPIAdapterIsReady = refl

sabioExportAcquisitionHasExecuted : Roadmap.sabioExportAcquisitionExecuted ≡ true
sabioExportAcquisitionHasExecuted = refl

underdeterminedDoesNotMeanMechanismFalse :
  Roadmap.BH4Phase4Boundary.underdeterminedMeansMechanismFalse
    Roadmap.canonicalBH4Phase4Boundary
  ≡ false
underdeterminedDoesNotMeanMechanismFalse = refl
