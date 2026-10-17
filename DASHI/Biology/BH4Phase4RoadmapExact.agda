module DASHI.Biology.BH4Phase4RoadmapExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.BH4QuantitativeAcquisitionExact as Acquisition
import DASHI.Biology.BH4ExecutedSABIOReceiptExact as SABIO
import DASHI.Biology.BH4ExecutedSABIOAdjudicationReceiptExact as SABIOAdj
import DASHI.Biology.BH4ExecutedSIFTSReceiptExact as SIFTS
import DASHI.Biology.BH4FluxCandidateRankingExact as Ranking
import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Executed
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Core.GenericReceipt as Receipt

data BH4Phase : Set where
  identityAndProvenancePhase : BH4Phase
  literalReactionPhase : BH4Phase
  systemStateQuantitativePhase : BH4Phase
  mechanisticDiscriminationPhase : BH4Phase
  clinicalPromotionPhase : BH4Phase

currentBH4Phase : BH4Phase
currentBH4Phase = systemStateQuantitativePhase

data BH4Phase4Residual : Set where
  resolveNonFiniteMTORProteinReactionRepresentation : BH4Phase4Residual
  rankSABIOCandidatesByFluxRelevance : BH4Phase4Residual
  adjudicateSABIOKineticCandidatesIntoFluxBounds : BH4Phase4Residual
  translatePCBD1NOSPrimaryKineticsIntoReactionBounds : BH4Phase4Residual
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
  ∷ rankSABIOCandidatesByFluxRelevance
  ∷ adjudicateSABIOKineticCandidatesIntoFluxBounds
  ∷ translatePCBD1NOSPrimaryKineticsIntoReactionBounds
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

fluxCandidateRankingToolReady : Bool
fluxCandidateRankingToolReady = true

firstBoundedSIFTSAcquisitionExecuted : Bool
firstBoundedSIFTSAcquisitionExecuted = SIFTS.boundedAcquisitionExecuted SIFTS.canonicalExecutedSIFTSReceipt

boundedSIFTSStructuresExamined : Nat
boundedSIFTSStructuresExamined = SIFTS.executedStructuresExamined

boundedSIFTSMatchingSegments : Nat
boundedSIFTSMatchingSegments = SIFTS.executedMatchingSIFTSSegmentCount

legacySABIORestSurfaceRetired : Bool
legacySABIORestSurfaceRetired = true

sabioExportAcquisitionExecuted : Bool
sabioExportAcquisitionExecuted = SABIO.exportAcquisitionExecuted SABIO.canonicalExecutedSABIOReceipt

sabioProteinsCompleted : Nat
sabioProteinsCompleted = SABIO.executedSABIOProteinsCompleted

sabioProteinsWithEntries : Nat
sabioProteinsWithEntries = SABIO.executedSABIOProteinsWithEntries

sabioKineticEntryCount : Nat
sabioKineticEntryCount = SABIO.executedSABIOKineticEntryCount

sabioKineticParameterCount : Nat
sabioKineticParameterCount = SABIO.executedSABIOKineticParameterCount

sabioAcquisitionErrorCount : Nat
sabioAcquisitionErrorCount = SABIO.executedSABIOAcquisitionErrorCount

sabioFiniteReactionCandidateCoverage : Nat
sabioFiniteReactionCandidateCoverage = SABIOAdj.executedFiniteReactionCoverage

sabioMappedParameterCandidates : Nat
sabioMappedParameterCandidates = SABIOAdj.executedMappedParameterCandidateCount

sabioUnclassifiedParameterCandidates : Nat
sabioUnclassifiedParameterCandidates = SABIOAdj.executedUnclassifiedCount

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

expandedCoordinateCountExact : expandedQuantitativeCoordinateCount ≡ 56
expandedCoordinateCountExact = refl

sabioKineticEntriesExact : sabioKineticEntryCount ≡ 190
sabioKineticEntriesExact = refl

sabioKineticParametersExact : sabioKineticParameterCount ≡ 932
sabioKineticParametersExact = refl

sabioFiniteReactionCoverageExact : sabioFiniteReactionCandidateCoverage ≡ 10
sabioFiniteReactionCoverageExact = refl

sabioMappedCandidatesExact : sabioMappedParameterCandidates ≡ 875
sabioMappedCandidatesExact = refl

sabioUnclassifiedCandidatesExact : sabioUnclassifiedParameterCandidates ≡ 45
sabioUnclassifiedCandidatesExact = refl

firstFluxAttemptMissingBoundsExact : missingReactionFluxBounds ≡ 12
firstFluxAttemptMissingBoundsExact = refl

firstFluxAttemptMissingExchangeExact : missingExternalExchangeCoordinates ≡ 29
firstFluxAttemptMissingExchangeExact = refl

record BH4Phase4Boundary : Set where
  constructor bh4-phase4-boundary
  field
    underdeterminedMeansMechanismFalse : Bool
    underdeterminedMeansMechanismFalseIsFalse : underdeterminedMeansMechanismFalse ≡ false
    finitePanelExecutionPaysQuantitativeFlux : Bool
    finitePanelExecutionPaysQuantitativeFluxIsFalse : finitePanelExecutionPaysQuantitativeFlux ≡ false
    residualMTORReactionMayBeInsertedAsZeroColumn : Bool
    residualMTORReactionMayBeInsertedAsZeroColumnIsFalse : residualMTORReactionMayBeInsertedAsZeroColumn ≡ false
    candidateKineticEvidenceAutomaticallyPaysFluxBounds : Bool
    candidateKineticEvidenceAutomaticallyPaysFluxBoundsIsFalse : candidateKineticEvidenceAutomaticallyPaysFluxBounds ≡ false
    sabioCandidateCoverageAutomaticallyPaysFluxBounds : Bool
    sabioCandidateCoverageAutomaticallyPaysFluxBoundsIsFalse : sabioCandidateCoverageAutomaticallyPaysFluxBounds ≡ false
    rankedCandidateAutomaticallyPaysFluxBound : Bool
    rankedCandidateAutomaticallyPaysFluxBoundIsFalse : rankedCandidateAutomaticallyPaysFluxBound ≡ false
    boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSites : Bool
    boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSitesIsFalse : boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSites ≡ false
    phase4CompletionAutomaticallyPromotesDiseaseCausation : Bool
    phase4CompletionAutomaticallyPromotesDiseaseCausationIsFalse : phase4CompletionAutomaticallyPromotesDiseaseCausation ≡ false

open BH4Phase4Boundary public

canonicalBH4Phase4Boundary : BH4Phase4Boundary
canonicalBH4Phase4Boundary =
  bh4-phase4-boundary false refl false refl false refl false refl false refl false refl false refl false refl

canonicalBH4Phase4RoadmapReceipt : Receipt.GenericReceipt
canonicalBH4Phase4RoadmapReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Phase-4 quantitative system-state roadmap"
    "DASHI.Biology.BH4Phase4RoadmapExact"
    "executed 29x12 network -> 56-coordinate open system -> SIFTS 38/526 -> SABIO 190 rows -> 932 parameter objects -> 875 finite-column mappings across 10/12 reactions -> refined v2 classification with only 45 unclassified -> flux-relevance ranking tool"
    "closes SABIO acquisition, schema-aware extraction and candidate classification/coverage accounting; narrows the live work to ranked assay/context adjudication, PCBD1/NOS primary-kinetics translation, reaction-bound payment and exchange/state payment"
    "candidate kinetics, candidate coverage and rank are not in-vivo flux bounds; kcat requires enzyme abundance/state; SIFTS mapping is not catalytic function; underdetermination is neither mechanism truth nor falsity"
    "python3 scripts/run_bh4_phase4_maxcut.py"
