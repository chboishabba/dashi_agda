module DASHI.Reasoning.BlockedImplicationExperimentBackpropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- BLOCKED CLAIM -> MISSING OBLIGATION -> DESIGN REQUIREMENT -> INFORMATION MOVE
--
-- This is the backward half of the experimental implication cone. A desired
-- downstream assertion is not promoted because it is desirable; instead the
-- specific blocked edge is decomposed into the exact evidential obligation and
-- experimental coordinate that would need additional information.
------------------------------------------------------------------------

record BlockedImplicationTarget : Set where
  constructor blockedImplicationTarget
  field
    desiredNode : Cone.ImplicationNode
    blockingEdge : Cone.ImplicationEdge
    edgeTargetsDesiredNodeReference : String
    edgeIsBlocked : Cone.status blockingEdge ≡ Cone.blockedEdge
    desiredUseReference : String

open BlockedImplicationTarget public

record MissingDesignRequirement
    (target : BlockedImplicationTarget) : Set where
  constructor missingDesignRequirement
  field
    missingObligation : PNF.AssertionObligation
    missingSlot : Cone.ExperimentalDesignSlot
    currentFailureReference : String
    requiredEvidenceShapeReference : String
    nuisanceOrResidualReference : String
    closureCriterionReference : String

open MissingDesignRequirement public

------------------------------------------------------------------------
-- Candidate experiments/information moves are indexed by the hidden residual
-- space they refine. The candidate must explicitly name how it addresses the
-- missing obligation/slot; merely being an experiment is insufficient.
------------------------------------------------------------------------

record CandidateBackpropMove
    {Hidden : Set}
    {target : BlockedImplicationTarget}
    (requirement : MissingDesignRequirement target) : Set₁ where
  constructor candidateBackpropMove
  field
    move : Costed.ResidualInformationMove Hidden
    addressesObligationReference : String
    addressesDesignSlotReference : String
    expectedEvidenceReference : String
    calibrationReference : String
    residualAfterMoveReference : String
    promotionStillRequiresAuditReference : String

open CandidateBackpropMove public

candidateMoveCarriesRefinement :
  ∀ {Hidden target requirement} →
  CandidateBackpropMove {Hidden} {target} requirement →
  Costed.ResidualInformationMove Hidden
candidateMoveCarriesRefinement = move

------------------------------------------------------------------------
-- Candidate-set and costed selection wrappers.
------------------------------------------------------------------------

record BackpropExperimentMenu
    {Hidden : Set}
    (target : BlockedImplicationTarget)
    (requirement : MissingDesignRequirement target) : Set₂ where
  constructor backpropExperimentMenu
  field
    Candidate : Set
    candidateMove : Candidate → CandidateBackpropMove {Hidden} requirement
    candidateReference : Candidate → String
    menuCompletenessReference : String
    excludedMoveReference : String

open BackpropExperimentMenu public

record BackpropThresholdSelection
    {Hidden : Set}
    {target : BlockedImplicationTarget}
    {requirement : MissingDesignRequirement target}
    (menu : BackpropExperimentMenu {Hidden} target requirement) : Set₂ where
  constructor backpropThresholdSelection
  field
    threshold : Nat
    selectedCandidate : Candidate menu
    selectedMeetsThreshold :
      Costed.MeetsResidualGainThreshold
        (move (candidateMove menu selectedCandidate))
        threshold

    -- Minimality is expressed directly over the declared candidate menu.
    minimalCost :
      (alternative : Candidate menu) →
      Costed.MeetsResidualGainThreshold
        (move (candidateMove menu alternative))
        threshold →
      Costed.cost (move (candidateMove menu selectedCandidate))
      ≤ Costed.cost (move (candidateMove menu alternative))

    selectionReference : String
    consumerOrClaimReference : String

open BackpropThresholdSelection public

------------------------------------------------------------------------
-- Status boundary. A selected next experiment is a plan for acquiring missing
-- evidence; it is not itself a discharge/promotion receipt.
------------------------------------------------------------------------

data BackpropStage : Set where
  blockedClaimStage
  experimentSelectedStage
  evidenceAcquiredStage
  obligationReauditedStage
  implicationSupportedStage
  : BackpropStage

experimentSelectedNotSupported :
  experimentSelectedStage ≡ implicationSupportedStage → ⊥
experimentSelectedNotSupported ()

evidenceAcquiredNotAutomaticallySupported :
  evidenceAcquiredStage ≡ implicationSupportedStage → ⊥
evidenceAcquiredNotAutomaticallySupported ()

record BlockedImplicationBackpropBoundary : Set where
  constructor blockedImplicationBackpropBoundary
  field
    desiredClaimAutomaticallyCreatesExperiment : Bool
    desiredClaimAutomaticallyCreatesExperimentIsFalse :
      desiredClaimAutomaticallyCreatesExperiment ≡ false
    blockedEdgeMustNameMissingObligation : Bool
    blockedEdgeMustNameMissingObligationIsTrue :
      blockedEdgeMustNameMissingObligation ≡ true
    candidateMustAddressDesignCoordinate : Bool
    candidateMustAddressDesignCoordinateIsTrue :
      candidateMustAddressDesignCoordinate ≡ true
    candidateMustCarryResidualProgressWitness : Bool
    candidateMustCarryResidualProgressWitnessIsTrue :
      candidateMustCarryResidualProgressWitness ≡ true
    cheapestSelectedExperimentAutomaticallySupportsClaim : Bool
    cheapestSelectedExperimentAutomaticallySupportsClaimIsFalse :
      cheapestSelectedExperimentAutomaticallySupportsClaim ≡ false
    newEvidenceMustBeReauditedBeforePromotion : Bool
    newEvidenceMustBeReauditedBeforePromotionIsTrue :
      newEvidenceMustBeReauditedBeforePromotion ≡ true

canonicalBlockedImplicationBackpropBoundary :
  BlockedImplicationBackpropBoundary
canonicalBlockedImplicationBackpropBoundary =
  blockedImplicationBackpropBoundary
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
