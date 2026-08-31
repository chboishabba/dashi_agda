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

------------------------------------------------------------------------
-- An Aristotle observer collision is literally a discriminator-synthesis
-- collision on proof states.
------------------------------------------------------------------------

observerCollision :
  {G : Aristotle.SearchHypergraph} →
  (O : Aristotle.StateObserver G) →
  (left right : Aristotle.State G) →
  left Aristotle.≈[ O ] right →
  Discriminator.CurrentObserverCollision (Aristotle.observe O)
observerCollision O left right same =
  Discriminator.currentObserverCollision left right same

------------------------------------------------------------------------
-- A meta-search probe observes proof states.  Examples may include trying a
-- lemma family, exposing an extra normal form, querying an auxiliary prover, or
-- computing a residual/discriminator.  The probe is not itself an Aristotle
-- proof action unless an application supplies that separate bridge.
------------------------------------------------------------------------

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
    currentlyCollapsed : left Aristotle.≈[ O ] right
    separates :
      Discriminator.BundleSeparates (bundle probe) left right

open ProbeSeparatesObserverCollision public

------------------------------------------------------------------------
-- Minimal discriminator search is inherited directly from the generic
-- experiment-design owner.  Minimality is only among the explicitly declared
-- candidate probes.
------------------------------------------------------------------------

ProofDiscriminator :
  {G : Aristotle.SearchHypergraph} →
  (O : Aristotle.StateObserver G) →
  (Declared : Discriminator.ExperimentBundle (Aristotle.State G) → Set) →
  Set₁
ProofDiscriminator O Declared =
  Discriminator.MinimalDiscriminator (Aristotle.observe O) Declared

------------------------------------------------------------------------
-- Sequential proof experiments.
--
-- The terminal consumer need not identify the complete hidden proof state.  It
-- is enough that every state surviving the current evidence fibre agrees on
-- the declared downstream proof-search consumer.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Actionability bridge.
--
-- A discriminator can also be judged by whether its information move removes
-- an explicitly supplied obstruction.  No probability, scientific utility or
-- proof probability is inferred here.
------------------------------------------------------------------------

ProofSearchResolvingDiscriminator :
  {G : Aristotle.SearchHypergraph} →
  (problem : Choice.ActionabilityProblem) → Set₁
ProofSearchResolvingDiscriminator {G} problem =
  Discriminator.ActionabilityResolvingDiscriminator
    {World = Aristotle.State G} problem

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

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
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
