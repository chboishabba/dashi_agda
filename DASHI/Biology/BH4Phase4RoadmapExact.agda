module DASHI.Biology.BH4Phase4RoadmapExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.BH4ExecutedSABIOReceiptExact as SABIO
import DASHI.Biology.BH4ExecutedSABIOAdjudicationReceiptExact as SABIOAdj
import DASHI.Biology.BH4ExecutedSIFTSReceiptExact as SIFTS
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
  executeFluxPaymentPreparation : BH4Phase4Residual
  payAssayReactionIdentityGates : BH4Phase4Residual
  paySameObjectCompartmentTimeGates : BH4Phase4Residual
  payNormalizedFluxUnitGates : BH4Phase4Residual
  payKineticToFluxTranslationGates : BH4Phase4Residual
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
  ∷ executeFluxPaymentPreparation
  ∷ payAssayReactionIdentityGates
  ∷ paySameObjectCompartmentTimeGates
  ∷ payNormalizedFluxUnitGates
  ∷ payKineticToFluxTranslationGates
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

fluxCandidateRankingToolReady : Bool
fluxCandidateRankingToolReady = true

fluxPaymentPreparationToolReady : Bool
fluxPaymentPreparationToolReady = true

sabioKineticParameterCount : Nat
sabioKineticParameterCount = SABIO.executedSABIOKineticParameterCount

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

expandedQuantitativeCoordinateCount : Nat
expandedQuantitativeCoordinateCount = 56

wholeSystemFluxBalanceAttempted : Bool
wholeSystemFluxBalanceAttempted = true

firstJointFluxOutcome : Flux.FluxFeasibilityStatus
firstJointFluxOutcome = Flux.underdetermined

missingReactionFluxBounds : Nat
missingReactionFluxBounds = 12

missingExternalExchangeCoordinates : Nat
missingExternalExchangeCoordinates = 29

executedPanelDimensionsExact : executedPanelSpeciesCount ≡ 29
executedPanelDimensionsExact = refl

executedPanelReactionsExact : executedPanelReactionCount ≡ 12
executedPanelReactionsExact = refl

sabioKineticParametersExact : sabioKineticParameterCount ≡ 932
sabioKineticParametersExact = refl

sabioFiniteReactionCoverageExact : sabioFiniteReactionCandidateCoverage ≡ 10
sabioFiniteReactionCoverageExact = refl

sabioMappedCandidatesExact : sabioMappedParameterCandidates ≡ 875
sabioMappedCandidatesExact = refl

sabioUnclassifiedCandidatesExact : sabioUnclassifiedParameterCandidates ≡ 45
sabioUnclassifiedCandidatesExact = refl

record BH4Phase4Boundary : Set where
  constructor bh4-phase4-boundary
  field
    underdeterminedMeansMechanismFalse : Bool
    underdeterminedMeansMechanismFalseIsFalse : underdeterminedMeansMechanismFalse ≡ false
    candidateKineticEvidenceAutomaticallyPaysFluxBounds : Bool
    candidateKineticEvidenceAutomaticallyPaysFluxBoundsIsFalse : candidateKineticEvidenceAutomaticallyPaysFluxBounds ≡ false
    rankedCandidateAutomaticallyPaysFluxBound : Bool
    rankedCandidateAutomaticallyPaysFluxBoundIsFalse : rankedCandidateAutomaticallyPaysFluxBound ≡ false
    assaySpecificCapacityAutomaticallyPaysIntracellularFlux : Bool
    assaySpecificCapacityAutomaticallyPaysIntracellularFluxIsFalse : assaySpecificCapacityAutomaticallyPaysIntracellularFlux ≡ false
    turnoverCapacityAutomaticallyPaysFluxWithoutAbundance : Bool
    turnoverCapacityAutomaticallyPaysFluxWithoutAbundanceIsFalse : turnoverCapacityAutomaticallyPaysFluxWithoutAbundance ≡ false
    boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSites : Bool
    boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSitesIsFalse : boundedSIFTSAcquisitionAutomaticallyPaysCatalyticSites ≡ false
    phase4CompletionAutomaticallyPromotesDiseaseCausation : Bool
    phase4CompletionAutomaticallyPromotesDiseaseCausationIsFalse : phase4CompletionAutomaticallyPromotesDiseaseCausation ≡ false

open BH4Phase4Boundary public

canonicalBH4Phase4Boundary : BH4Phase4Boundary
canonicalBH4Phase4Boundary =
  bh4-phase4-boundary false refl false refl false refl false refl false refl false refl false refl

canonicalBH4Phase4RoadmapReceipt : Receipt.GenericReceipt
canonicalBH4Phase4RoadmapReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Phase-4 quantitative system-state roadmap"
    "DASHI.Biology.BH4Phase4RoadmapExact"
    "executed 29x12 network -> 56-coordinate open system -> SABIO 932 parameters -> 875 finite-column mappings across 10/12 reactions -> refined classification -> ranked candidate queue -> fail-closed flux-payment preparation"
    "closes acquisition, extraction, classification and ranking architecture; narrows the live work to paying reaction identity, compartment/time, unit-normalization and kinetic-to-flux translation gates plus the 29 exchange bounds"
    "assay-specific Vmax is not intracellular flux; kcat requires enzyme abundance/state; Km/Kd/Ki do not define magnitude alone; primary-literature kinetics and SIFTS mappings remain non-promoting evidence"
    "python3 scripts/run_bh4_phase4_maxcut.py"
