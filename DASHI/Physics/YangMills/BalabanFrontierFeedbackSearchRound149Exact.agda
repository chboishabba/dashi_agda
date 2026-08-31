{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFrontierFeedbackSearchRound149Exact where

------------------------------------------------------------------------
-- ROUND149: TWO-CHANNEL FEEDBACK -- SEARCH RESOLUTION != THEOREM CLOSURE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as R146

-- The Aristotle ledger is specialized literally to the live Balaban leaves.
frontierLedger :
  (R146.BalabanFrontierLeaf → Aristotle.LemmaStatus) →
  Aristotle.LemmaLedger
frontierLedger status = record
  { Aristotle.LemmaLedger.LemmaId = R146.BalabanFrontierLeaf
  ; Aristotle.LemmaLedger.status = status
  }

FrontierLeafProved :
  (status : R146.BalabanFrontierLeaf → Aristotle.LemmaStatus) →
  R146.BalabanFrontierLeaf → Set
FrontierLeafProved status leaf =
  Aristotle.ProvedIn (frontierLedger status) leaf

UnifiedSectorClosed :
  (status : R146.BalabanFrontierLeaf → Aristotle.LemmaStatus) → Set
UnifiedSectorClosed status = FrontierLeafProved status R146.unifiedSectorStressRecovery

-- Same identifier space across iterations: only statuses change.  Already-proved
-- leaves must be retained, exactly matching Aristotle's formal-feedback rule.
record BalabanFrontierFeedback
    (oldStatus newStatus : R146.BalabanFrontierLeaf → Aristotle.LemmaStatus) : Set₁ where
  field
    preservesProvedLeaf : ∀ leaf →
      FrontierLeafProved oldStatus leaf →
      FrontierLeafProved newStatus leaf

open BalabanFrontierFeedback public

asAristotleFeedback :
  ∀ {oldStatus newStatus} →
  BalabanFrontierFeedback oldStatus newStatus →
  Aristotle.FeedbackRefinement
    (frontierLedger oldStatus) (frontierLedger newStatus)
asAristotleFeedback dataSet = record
  { Aristotle.FeedbackRefinement.castId = λ leaf → leaf
  ; Aristotle.FeedbackRefinement.preservesProved =
      preservesProvedLeaf dataSet
  }

unifiedSectorClosureMonotone :
  ∀ {oldStatus newStatus}
    (feedback : BalabanFrontierFeedback oldStatus newStatus) →
  UnifiedSectorClosed oldStatus → UnifiedSectorClosed newStatus
unifiedSectorClosureMonotone feedback =
  Aristotle.provedKnowledgeMonotone
    (asAristotleFeedback feedback) R146.unifiedSectorStressRecovery

------------------------------------------------------------------------
-- Costed experiment/search channel.
------------------------------------------------------------------------

frontierActionabilityProblem :
  (leaf : R146.BalabanFrontierLeaf) →
  (Resolves : Choice.InformationMove → R146.BalabanFrontierLeaf → Set) →
  String → String → String →
  Choice.ActionabilityProblem
frontierActionabilityProblem leaf resolves obstructionRef consumerRef authorityRef = record
  { Choice.ActionabilityProblem.Obstruction = R146.BalabanFrontierLeaf
  ; Choice.ActionabilityProblem.currentObstruction = leaf
  ; Choice.ActionabilityProblem.Resolves = resolves
  ; Choice.ActionabilityProblem.obstructionReference = obstructionRef
  ; Choice.ActionabilityProblem.decisionConsumerReference = consumerRef
  ; Choice.ActionabilityProblem.authorityReference = authorityRef
  }

record CostedBalabanFrontierResolution : Set₁ where
  field
    targetLeaf : R146.BalabanFrontierLeaf
    problem : Choice.ActionabilityProblem
    problemTargetsLeaf : Choice.currentObstruction problem ≡ targetLeaf
    DeclaredMove : Choice.InformationMove → Set
    cheapestAuthorisingMove :
      Choice.CheapestAuthorisingInformationMove problem DeclaredMove

open CostedBalabanFrontierResolution public

-- The planner can establish that an information move resolved an obstruction and
-- authorised a *search decision*.  There is intentionally no function here from
-- CostedBalabanFrontierResolution to FrontierLeafProved.

record BalabanFrontierFeedbackBoundary : Set where
  constructor balabanFrontierFeedbackBoundary
  field
    resolvingSearchObstructionAutomaticallyMarksLeafProved : Agda.Builtin.Bool.Bool
    resolvingSearchObstructionAutomaticallyMarksLeafProvedIsFalse :
      resolvingSearchObstructionAutomaticallyMarksLeafProved ≡ Agda.Builtin.Bool.false
    provedLeafMayBeForgottenByFeedbackIteration : Agda.Builtin.Bool.Bool
    provedLeafMayBeForgottenByFeedbackIterationIsFalse :
      provedLeafMayBeForgottenByFeedbackIteration ≡ Agda.Builtin.Bool.false

canonicalBalabanFrontierFeedbackBoundary : BalabanFrontierFeedbackBoundary
canonicalBalabanFrontierFeedbackBoundary =
  balabanFrontierFeedbackBoundary Agda.Builtin.Bool.false refl Agda.Builtin.Bool.false refl

balabanFrontierFeedbackSearchLevel : ProofLevel
balabanFrontierFeedbackSearchLevel = machineChecked
