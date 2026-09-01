module DASHI.Reasoning.AristotleExperimentalBranchMergeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle

------------------------------------------------------------------------
-- ARISTOTLE SEARCH-BRANCH RECONCILIATION
--
-- Proved lemma knowledge is monotone under Aristotle FeedbackRefinement.  This
-- makes a common-refinement / join-like merge legitimate for the lemma ledger.
-- It does NOT make arbitrary proof states, tactic actions, local contexts, or
-- observer fibres CRDT-joinable.
------------------------------------------------------------------------

data MergeStrategy : Set where
  fastForward
  commonRefinement
  threeWayReconciliation
  monotoneKnowledgeJoin
  conflictReview
  : MergeStrategy

record CommonLemmaRefinement
    (left right merged : Aristotle.LemmaLedger) : Set₁ where
  constructor common-lemma-refinement
  field
    leftIntoMerged : Aristotle.FeedbackRefinement left merged
    rightIntoMerged : Aristotle.FeedbackRefinement right merged
    strategy : MergeStrategy
    mergeReference : String

open CommonLemmaRefinement public

leftProvedKnowledgeSurvivesMerge :
  {left right merged : Aristotle.LemmaLedger} →
  (R : CommonLemmaRefinement left right merged) →
  (lemma : Aristotle.LemmaId left) →
  Aristotle.ProvedIn left lemma →
  Aristotle.ProvedIn merged
    (Aristotle.castId (leftIntoMerged R) lemma)
leftProvedKnowledgeSurvivesMerge R lemma =
  Aristotle.provedKnowledgeMonotone (leftIntoMerged R) lemma

rightProvedKnowledgeSurvivesMerge :
  {left right merged : Aristotle.LemmaLedger} →
  (R : CommonLemmaRefinement left right merged) →
  (lemma : Aristotle.LemmaId right) →
  Aristotle.ProvedIn right lemma →
  Aristotle.ProvedIn merged
    (Aristotle.castId (rightIntoMerged R) lemma)
rightProvedKnowledgeSurvivesMerge R lemma =
  Aristotle.provedKnowledgeMonotone (rightIntoMerged R) lemma

------------------------------------------------------------------------
-- Proof-state reconciliation requires an independent semantic receipt.
------------------------------------------------------------------------

record ProofStateMergeReceipt
    (G : Aristotle.SearchHypergraph)
    (O : Aristotle.StateObserver G)
    (left right merged : Aristotle.State G) : Set₁ where
  constructor proof-state-merge-receipt
  field
    leftObservablePreserved :
      Aristotle.observe O merged ≡ Aristotle.observe O left
    rightObservableCompatible :
      Aristotle.observe O left ≡ Aristotle.observe O right
    proofTransportSound : Aristotle.QuotientSound G O
    reconciliationReference : String

open ProofStateMergeReceipt public

leftProofTransportsToMerged :
  {G : Aristotle.SearchHypergraph}
  {O : Aristotle.StateObserver G}
  {left right merged : Aristotle.State G} →
  (R : ProofStateMergeReceipt G O left right merged) →
  Aristotle.StateProved G left →
  Aristotle.StateProved G merged
leftProofTransportsToMerged R =
  Aristotle.transportProof
    (proofTransportSound R)
    (sym (leftObservablePreserved R))

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record AristotleBranchMergeBoundary : Set where
  constructor aristotle-branch-merge-boundary
  field
    provedLemmaKnowledgeCanUseCommonRefinementJoin : Bool
    provedLemmaKnowledgeCanUseCommonRefinementJoinIsTrue :
      provedLemmaKnowledgeCanUseCommonRefinementJoin ≡ true

    arbitraryProofStatesAreCRDTJoinable : Bool
    arbitraryProofStatesAreCRDTJoinableIsFalse :
      arbitraryProofStatesAreCRDTJoinable ≡ false

    observedStateEqualityAloneAlwaysTransportsProof : Bool
    observedStateEqualityAloneAlwaysTransportsProofIsFalse :
      observedStateEqualityAloneAlwaysTransportsProof ≡ false

    quotientSoundnessRequiredForProofTransport : Bool
    quotientSoundnessRequiredForProofTransportIsTrue :
      quotientSoundnessRequiredForProofTransport ≡ true

    mergeStrategyMayBeChosenIndependentlyOfProofSemantics : Bool
    mergeStrategyMayBeChosenIndependentlyOfProofSemanticsIsFalse :
      mergeStrategyMayBeChosenIndependentlyOfProofSemantics ≡ false

canonicalAristotleBranchMergeBoundary : AristotleBranchMergeBoundary
canonicalAristotleBranchMergeBoundary =
  aristotle-branch-merge-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
