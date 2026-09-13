module DASHI.Interop.GodsEyeViewWorldResearchFrontierActionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact as Loop

------------------------------------------------------------------------
-- WORLD RESEARCH FRONTIER ACTION
--
-- #815 owns the analogous legal feedback vocabulary on its branch.  #823 must
-- remain independently typecheckable until that branch lands, so this owner
-- exposes the world-side action now and records the intended semantic weld.
------------------------------------------------------------------------

data WorldFrontierAction : Set where
  recomputeWorldFrontier : WorldFrontierAction
  continueWorldResearch : WorldFrontierAction
  expandWorldResearch : WorldFrontierAction
  reopenWorldForDefeater : WorldFrontierAction

frontierAction : Loop.ObservationReturnDisposition → WorldFrontierAction
frontierAction Loop.payPrerequisite = recomputeWorldFrontier
frontierAction Loop.keepOpen = continueWorldResearch
frontierAction Loop.splitDiagnosis = expandWorldResearch
frontierAction Loop.reactivateDiagnosis = reopenWorldForDefeater

paymentRecomputes : frontierAction Loop.payPrerequisite ≡ recomputeWorldFrontier
paymentRecomputes = refl

openContinues : frontierAction Loop.keepOpen ≡ continueWorldResearch
openContinues = refl

splitExpands : frontierAction Loop.splitDiagnosis ≡ expandWorldResearch
splitExpands = refl

reactivationReopens : frontierAction Loop.reactivateDiagnosis ≡ reopenWorldForDefeater
reactivationReopens = refl

record WorldResearchFrontierTransition : Set₁ where
  constructor world-research-frontier-transition
  field
    recomputedConcern : Loop.RecomputedWorldConcern
    selectedAction : WorldFrontierAction
    actionMatchesDisposition :
      selectedAction ≡ frontierAction (Loop.returnDisposition recomputedConcern)
    nextFrontierReference : String
    oldEvidenceHistoryPreservedReference : String
    minimalCutOrFirstMissingRecomputedReference : String
    nextCandidateSetReference : String
    transitionReference : String

open WorldResearchFrontierTransition public

------------------------------------------------------------------------
-- Compatibility contract for the later #815 weld.
------------------------------------------------------------------------

record LegalFeedbackCompatibilityBoundary : Set where
  constructor legal-feedback-compatibility-boundary
  field
    payMapsToRecompute : Bool
    payMapsToRecomputeIsTrue : payMapsToRecompute ≡ true
    keepOpenMapsToContinue : Bool
    keepOpenMapsToContinueIsTrue : keepOpenMapsToContinue ≡ true
    splitMapsToExpand : Bool
    splitMapsToExpandIsTrue : splitMapsToExpand ≡ true
    reactivateMapsToReopenForDefeater : Bool
    reactivateMapsToReopenForDefeaterIsTrue : reactivateMapsToReopenForDefeater ≡ true
    branchLocalCompatibilityIsSameObjectProof : Bool
    branchLocalCompatibilityIsSameObjectProofIsFalse :
      branchLocalCompatibilityIsSameObjectProof ≡ false

canonicalLegalFeedbackCompatibilityBoundary : LegalFeedbackCompatibilityBoundary
canonicalLegalFeedbackCompatibilityBoundary =
  legal-feedback-compatibility-boundary true refl true refl true refl true refl false refl

data SemanticCompatibilityAutomaticallyProvesCrossBranchSameObject : Set where
semanticCompatibilityDoesNotProveCrossBranchSameObject :
  SemanticCompatibilityAutomaticallyProvesCrossBranchSameObject → ⊥
semanticCompatibilityDoesNotProveCrossBranchSameObject ()
