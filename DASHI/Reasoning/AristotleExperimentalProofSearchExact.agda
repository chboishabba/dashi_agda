module DASHI.Reasoning.AristotleExperimentalProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential

------------------------------------------------------------------------
-- ARISTOTLE x EXPERIMENTAL-DESIGN PROOF SEARCH
--
-- Aristotle owns the proof-validity/search hypergraph semantics.  DASHI's
-- experimental-design layer owns a different question: which additional
-- observation/probe should be run next when the current observer collapses
-- states that matter differently to a downstream consumer?
--
-- This file composes those layers without attributing the experimental-design
-- policy to the Harmonic Team paper and without replacing StateProved /
-- ActionProved with a heuristic score.
------------------------------------------------------------------------

observerCollision :
  {G : Aristotle.SearchHypergraph} →
  (O : Aristotle.StateObserver G) →
  (left right : Aristotle.State G) →
  Aristotle._≈[_]_ left O right →
  Discriminator.CurrentObserverCollision (Aristotle.observe O)
observerCollision O left right same =
  Discriminator.currentObserverCollision left right same

record AristotleProofProbe
    (G : Aristotle.SearchHypergraph) : Set₁ where
  constructor aristotle-proof-probe
  field
    bundle : Discriminator.ExperimentBundle (Aristotle.State G)
    probeReference : String
    proofActionBridgeReference : String

open AristotleProofProbe public

record ProbeSeparatesObserverCollision
    {G : Aristotle.SearchHypergraph}
    (O : Aristotle.StateObserver G)
    (probe : AristotleProofProbe G)
    (left right : Aristotle.State G) : Set where
  constructor probe-separates-observer-collision
  field
    currentlyCollapsed : Aristotle._≈[_]_ left O right
    separates :
      Discriminator.BundleSeparates (bundle probe) left right

open ProbeSeparatesObserverCollision public

ProofDiscriminator :
  {G : Aristotle.SearchHypergraph} →
  (O : Aristotle.StateObserver G) →
  (Declared : Discriminator.ExperimentBundle (Aristotle.State G) → Set) →
  Set₁
ProofDiscriminator O Declared =
  Discriminator.MinimalDiscriminator (Aristotle.observe O) Declared

SequentialProofExperimentPlan :
  {G : Aristotle.SearchHypergraph} {Prediction : Set} →
  (consumer : Aristotle.State G → Prediction) →
  (compatible : Aristotle.State G → Set) →
  Set₁
SequentialProofExperimentPlan = Sequential.SequentialConsumerPlan

CertifiedSequentialProofExperimentPlan :
  {G : Aristotle.SearchHypergraph} {Prediction : Set} →
  (consumer : Aristotle.State G → Prediction) →
  (compatible : Aristotle.State G → Set) →
  Set₂
CertifiedSequentialProofExperimentPlan = Sequential.CertifiedSequentialPlan

ProofSearchResolvingDiscriminator :
  {G : Aristotle.SearchHypergraph} →
  (problem : Choice.ActionabilityProblem) → Set₁
ProofSearchResolvingDiscriminator {G} problem =
  Discriminator.ActionabilityResolvingDiscriminator
    {World = Aristotle.State G} problem

record AristotleExperimentalProofSearchBoundary : Set where
  constructor aristotle-experimental-proof-search-boundary
  field
    experimentalDesignPolicyClaimedByAristotlePaper : Bool
    experimentalDesignPolicyClaimedByAristotlePaperIsFalse :
      experimentalDesignPolicyClaimedByAristotlePaper ≡ false
    searchPolicyReplacesProofValiditySemantics : Bool
    searchPolicyReplacesProofValiditySemanticsIsFalse :
      searchPolicyReplacesProofValiditySemantics ≡ false
    observerCollisionCanBeTargetedByDiscriminator : Bool
    observerCollisionCanBeTargetedByDiscriminatorIsTrue :
      observerCollisionCanBeTargetedByDiscriminator ≡ true
    nextProofExperimentMayDependOnObservedOutcome : Bool
    nextProofExperimentMayDependOnObservedOutcomeIsTrue :
      nextProofExperimentMayDependOnObservedOutcome ≡ true
    terminalSearchConsumerRequiresFullStateIdentity : Bool
    terminalSearchConsumerRequiresFullStateIdentityIsFalse :
      terminalSearchConsumerRequiresFullStateIdentity ≡ false
    leastCostClaimRequiresDeclaredComparisonClass : Bool
    leastCostClaimRequiresDeclaredComparisonClassIsTrue :
      leastCostClaimRequiresDeclaredComparisonClass ≡ true

canonicalAristotleExperimentalProofSearchBoundary :
  AristotleExperimentalProofSearchBoundary
canonicalAristotleExperimentalProofSearchBoundary =
  aristotle-experimental-proof-search-boundary
    false refl false refl true refl true refl false refl true refl
