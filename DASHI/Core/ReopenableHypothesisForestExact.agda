module DASHI.Core.ReopenableHypothesisForestExact where

------------------------------------------------------------------------
-- REOPENABLE HYPOTHESIS FOREST
--
-- Cross-project law (Animalexic / SeaMeInIt / LES): removing a hypothesis from
-- the active frontier is not a refutation.  Budget deferral and unresolved
-- ambiguity remain reopenable states; refutation requires an explicit
-- contradiction witness for the hypothesis itself.
--
-- This is a DASHI construction.  It intentionally does not commit every domain
-- to one statistical belief calculus: probabilities, Dempster--Shafer masses,
-- geometric residuals and environmental source scores may inhabit separate
-- evidence adapters while sharing the transition law below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- P / Q / R semantics.
------------------------------------------------------------------------

data DormancyReason : Set where
  budgetDeferred : DormancyReason
  ambiguityUnresolved : DormancyReason
  dependencyChanged : DormancyReason
  fidelityPending : DormancyReason
  policyChanged : DormancyReason

data HypothesisStatus : Set where
  active : HypothesisStatus
  reopenable : DormancyReason → HypothesisStatus
  refuted : HypothesisStatus

------------------------------------------------------------------------
-- Refutation is proof-bearing.  In particular there is deliberately no
-- constructor `reopenable -> refuted`: an inactive alternative must first be
-- reopened and evaluated, or a domain-specific refutation proof must be
-- supplied against the hypothesis carrier itself.
------------------------------------------------------------------------

record HypothesisSemantics (Hypothesis : Set) : Set₁ where
  constructor hypothesisSemantics
  field
    Refutation : Hypothesis → Set
    ReopeningEvidence : DormancyReason → Hypothesis → Set

open HypothesisSemantics public

data HypothesisTransition
    {Hypothesis : Set}
    (semantics : HypothesisSemantics Hypothesis)
    (hypothesis : Hypothesis) :
    HypothesisStatus → HypothesisStatus → Set where
  defer :
    (reason : DormancyReason) →
    HypothesisTransition semantics hypothesis active (reopenable reason)
  reopen :
    (reason : DormancyReason) →
    ReopeningEvidence semantics reason hypothesis →
    HypothesisTransition semantics hypothesis (reopenable reason) active
  refuteActive :
    Refutation semantics hypothesis →
    HypothesisTransition semantics hypothesis active refuted
  remainRefuted :
    HypothesisTransition semantics hypothesis refuted refuted

------------------------------------------------------------------------
-- The negative theorem is structural: no direct dormant-to-refuted transition
-- exists in the calculus.  This prevents beam pruning, scenario omission or an
-- inactive semantic hypothesis from silently becoming counterevidence.
------------------------------------------------------------------------

noDirectDormantRefutation :
  ∀ {Hypothesis}
    {semantics : HypothesisSemantics Hypothesis}
    {hypothesis : Hypothesis}
    {reason : DormancyReason} →
  HypothesisTransition semantics hypothesis (reopenable reason) refuted →
  ⊥
noDirectDormantRefutation ()

------------------------------------------------------------------------
-- Forest entries keep status separate from the payload and any domain score.
------------------------------------------------------------------------

record HypothesisEntry (Hypothesis Score : Set) : Set where
  constructor hypothesisEntry
  field
    hypothesis : Hypothesis
    status : HypothesisStatus
    score : Score

open HypothesisEntry public

record ReopenableHypothesisBoundary : Set where
  constructor reopenableHypothesisBoundary
  field
    inactiveDoesNotMeanRefuted : Bool
    refutationRequiresDomainWitness : Bool
    dormantAlternativeCanReturnToActive : Bool
    scoringSemanticsRemainDomainSpecific : Bool

canonicalReopenableHypothesisBoundary : ReopenableHypothesisBoundary
canonicalReopenableHypothesisBoundary =
  reopenableHypothesisBoundary true true true true
