module DASHI.Biology.BH4Phase4RoadmapExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.BH4QuantitativeAcquisitionExact as Acquisition
import DASHI.Biology.BH4ExecutedSABIOReceiptExact as SABIO
import DASHI.Biology.BH4ExecutedSIFTSReceiptExact as SIFTS
import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Executed
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Phase-4 roadmap after live panel chemistry, bounded SIFTS acquisition,
-- successful SABIO export acquisition, and the first joint-flux execution.
------------------------------------------------------------------------

data BH4Phase : Set where
  identityAndProvenancePhase : BH4Phase
  literalReactionPhase : BH4Phase
  systemStateQuantitativePhase : BH4Phase
  mechanisticDiscriminationPhase : BH4Phase
  clinicalPromotionPhase : BH4Phase

currentBH4Phase : BH4Phase
currentBH4Phase = systemStateQuantitativePhase

data BH4Phase4Residual : Set where
  executePanelRheaAcquisition : BH4Phase4Residual
  promoteFinitePanelReactionReceipts : BH4Phase4Residual
  resolveNonFiniteMTORProteinReactionRepresentation : BH4Phase4Residual
  normalizeSABIOKineticParameterCandidates : BH4Phase4Residual
  adjudicateSABIOKineticCandidatesIntoFluxBounds : BH4Phase4Residual
  adjudicatePDBSIFTSResidueSiteWitnesses : BH4Phase4Residual
  payReactionSpecificFluxBounds : BH4Phase4Residual
  payCompartmentSpecificBH4BH2RedoxState : BH4Phase4Residual
  paySimultaneousConsumerDemand : BH4Phase4Residual
  payTransportOxidationExchangeVector : BH4Phase4Residual
  payIsoformSpecificNOSCouplingTransitions : BH4Phase4Residual
  payUpstreamToTSC2SameObjectTransport : BH4Phase4Residual
  discriminateAlternativeMechanisms : BH4Phase4Residual

livePhase4Residuals : List BH4Phase4Residual
livePhase4Residuals =
  resolveNonFiniteMTORProteinReactionRepresentation
  ∷ normalizeSABIOKineticParameterCandidates
  ∷ adjudicateSABIOKineticCandidatesIntoFluxBounds
  ∷ adjudicatePDBSIFTSResidueSiteWitnesses
  ∷ payReactionSpecificFluxBounds
  ∷ payCompartmentSpecificBH4BH2RedoxState
  ∷ paySimultaneousConsumerDemand
  ∷ payTransportOxidationExchangeVector
  ∷ payIsoformSpecificNOSCouplingTransitions
  ∷ payUpstreamToTSC2SameObjectTransport
  ∷ discriminateAlternativeMechanisms
  ∷ []

panelRheaAcquisitionExecuted : Bool
panelRheaAcquisitionExecuted = Executed.acquisitionExecuted Executed.canonicalExecutedPanelReactionReceipt

finitePanelReactionPromotionClosed : Bool
finitePanelReactionPromotionClosed = true

quantitativeAcquisitionToolingReady : Bool
quantitativeAcquisitionToolingReady = true

intervalFluxSolverReady : Bool
intervalFluxSolverReady = true

firstBoundedSIFTSAcquisitionExecuted : Bool
firstBoundedSIFTSAcquisitionExecuted = SIFTS.boundedAcquisitionExecuted SIFTS.canonicalExecutedSIFTSReceipt

boundedSIFTSStructuresExamined : Nat
boundedSIFTSStructuresExamined = SIFTS.structuresExamined SIFTS.canonicalExecutedSIFTSReceipt

boundedSIFTSMatchingSegments : Nat
boundedSIFTSMatchingSegments = SIFTS.matchingSIFTSSegmentCount SIFTS.canonicalExecutedSIFTSReceipt

boundedSIFTSProteinsWithPDBLinks : Nat
boundedSIFTSProteinsWithPDBLinks = SIFTS.proteinsWithUniProtPDBLinks SIFTS.canonicalExecutedSIFTSReceipt

boundedSIFTSProteinsWithMatchingSegments : Nat
boundedSIFTSProteinsWithMatchingSegments = SIFTS.proteinsWithMatchingSegments SIFTS.canonicalExecutedSIFTSReceipt

legacySABIORestSurfaceRetired : Bool
legacySABIORestSurfaceRetired = true

sabioExportAPIAdapterReady : Bool
sabioExportAPIAdapterReady = true

sabioExportAcquisitionExecuted : Bool
sabioExportAcquisitionExecuted = SABIO.exportAcquisitionExecuted SABIO.canonicalExecutedSABIOReceipt

sabioProteinsCompleted : Nat
sabioProteinsCompleted = SABIO.executedSABIOProteinsCompleted

sabioProteinsWithEntries : Nat
sabioProteinsWithEntries = SABIO.executedSABIOProteinsWithEntries

sabioKineticEntryCount : Nat
sabioKineticEntryCount = SABIO.executedSABIOKineticEntryCount

sabioAcquisitionErrorCount : Nat
sabioAcquisitionErrorCount = SABIO.executedSABIOAcquisitionErrorCount

sabioParameterSchemaRecountRequired : Bool
sabioParameterSchemaRecountRequired = SABIO.parameterSchemaRecountRequired SABIO.canonicalExecutedSABIOReceipt

executedPanelSpeciesCount : Nat
executedPanelSpeciesCount = Matrix.executedPanelSpeciesCount

executedPanelReactionCount : Nat
executedPanelReactionCount = Matrix.executedPanelReactionCount

firstQuantitativeCoordinateCount : Nat
firstQuantitativeCoordinateCount = 27

expandedQuantitativeCoordinateCount : Nat
expandedQuantitativeCoordinateCount = 56

wholeSystemFluxBalanceAttempted : Bool
wholeSystemFluxBalanceAttempted = true

firstJointFluxOutcome : Flux.FluxFeasibilityStatus
firstJointFluxOutcome = Flux.underdetermined

missingReactionFluxBounds : Nat
missingReactionFluxBounds = 12

missingReactionFluxValues : Nat
missingReactionFluxValues = 12

missingExternalExchangeCoordinates : Nat
missingExternalExchangeCoordinates = 29

executedPanelDimensionsExact : executedPanelSpeciesCount ≡ 29
executedPanelDimensionsExact = refl

executedPanelReactionsExact : executedPanelReactionCount ≡ 12
executedPanelReactionsExact = refl

firstCoordinateCountExact : firstQuantitativeCoordinateCount ≡ 27
firstCoordinateCountExact = refl

expandedCoordinateCountExact : expandedQuantitativeCoordinateCount ≡ 56
expandedCoordinateCountExact = refl

boundedSIFTSStructuresExact : boundedSIFTSStructuresExamined ≡ 38
boundedSIFTSStructuresExact = refl

boundedSIFTSSegmentsExact : boundedSIFTSMatchingSegments ≡ 526
boundedSIFTSSegmentsExact = refl

boundedSIFTSLinkedProteinsExact : boundedSIFTSProteinsWithPDBLinks ≡ 14
boundedSIFTSLinkedProteinsExact = refl

boundedSIFTSMatchingProteinsExact : boundedSIFTSProteinsWithMatchingSegments ≡ 13
boundedSIFTSMatchingProteinsExact = refl

sabioProteinsCompletedExact : sabioProteinsCompleted ≡ 16
sabioProteinsCompletedExact = refl

sabioProteinsWithEntriesExact : sabioProteinsWithEntries ≡ 11
sabioProteinsWithEntriesExact = refl

sabioKineticEntriesExact : sabioKineticEntryCount ≡ 190
sabioKineticEntriesExact = refl

sabioErrorsExact : sabioAcquisitionErrorCount ≡ 0
sabioErrorsExact = refl

firstFluxAttemptMissingBoundsExact : missingReactionFluxBounds ≡ 12
firstFluxAttemptMissingBoundsExact = refl

firstFluxAttemptMissingValuesExact : missingReactionFluxValues ≡ 12
firstFluxAttemptMissingValuesExact = refl

firstFluxAttemptMissingExchangeExact : missingExternalExchangeCoordinates ≡ 29
firstFluxAttemptMissingExchangeExact = refl

record BH4Phase4Boundary : Set where
  constructor bh4-phase4-boundary
  field
    underdeterminedMeansMechanismFalse : Bool
    underdeterminedMeansMechanismFalseIsFalse : underdeterminedMeansMechanismFalse ≡ false
    underdeterminedMeansMechanismTrue : Bool
    underdeterminedMeansMechanismTrueIsFalse : underdeterminedMeansMechanismTrue ≡ false
    finitePanelExecutionPaysQuantitativeFlux : Bool
    finitePanelExecutionPaysQuantitativeFluxIsFalse :
      finitePanelExecutionPaysQuantitativeFlux ≡ false
    residualMTORReactionMayBeInsertedAsZeroColumn : Bool
    residualMTORReactionMayBeInsertedAsZeroColumnIsFalse :
      residualMTORReactionMayBeInsertedAsZeroColumn ≡ false
    candidateKineticEvidenceAutomaticallyPaysFluxBounds : Bool
    candidateKineticEvidenceAutomaticallyPaysFluxBoundsIsFalse :
      candidateKineticEvidenceAutomaticallyPaysFluxBounds ≡ false
    sabioExportCoverageAutomaticallyPaysFluxBounds : Bool
    sabioExportCoverageAutomaticallyPaysFluxBoundsIsFalse :
      sabioExportCoverageAutomaticallyPaysFluxBounds ≡ false
    boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSites : Bool
    boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSitesIsFalse :
      boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSites ≡ false
    phase4CompletionAutomaticallyPromotesDiseaseCausation : Bool
    phase4CompletionAutomaticallyPromotesDiseaseCausationIsFalse :
      phase4CompletionAutomaticallyPromotesDiseaseCausation ≡ false
    phase4CompletionAutomaticallyPromotesClinicalAction : Bool
    phase4CompletionAutomaticallyPromotesClinicalActionIsFalse :
      phase4CompletionAutomaticallyPromotesClinicalAction ≡ false

open BH4Phase4Boundary public

canonicalBH4Phase4Boundary : BH4Phase4Boundary
canonicalBH4Phase4Boundary =
  bh4-phase4-boundary
    false refl false refl false refl false refl false refl false refl false refl false refl false refl

canonicalBH4Phase4RoadmapReceipt : Receipt.GenericReceipt
canonicalBH4Phase4RoadmapReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Phase-4 quantitative system-state roadmap"
    "DASHI.Biology.BH4Phase4RoadmapExact"
    "executed 16-protein panel -> 24 Rhea links -> 29x12 finite network -> 56-coordinate open-system problem -> SIFTS receipt (38 structures, 526 segments) -> SABIO receipt (190 kinetic rows across 11 proteins)"
    "closes reaction, bounded structural-mapping and SABIO export acquisition; advances the live frontier to schema-aware kinetic-parameter normalization, condition/source adjudication and justified reaction/exchange interval payment"
    "SIFTS mapping is not catalytic-site function; SABIO export rows are not in-vivo flux bounds; historical zero parameter count was a parser-schema miss; underdetermination is neither mechanism truth nor falsity; Phase-4 closure does not establish disease or clinical causation"
    "python3 scripts/run_bh4_phase4_maxcut.py"
