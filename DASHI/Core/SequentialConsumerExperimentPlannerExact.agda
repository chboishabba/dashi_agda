module DASHI.Core.SequentialConsumerExperimentPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis

------------------------------------------------------------------------
-- SEQUENTIAL CONSUMER-RELATIVE EXPERIMENT PLANNING
--
-- A one-shot experiment need not close the declared prediction/decision
-- consumer.  This module therefore makes the next experiment depend on the
-- realised observation and carries the refined compatible-state fibre down the
-- corresponding branch.
--
-- The terminal condition is consumer point-identifiability, not identity of the
-- full hidden world state.  No probability distribution or expected utility is
-- assumed; cost below is a worst-case proof bound over all declared outcomes.
------------------------------------------------------------------------

private
  variable
    World Prediction : Set

RefineByBundle :
  (compatible : World → Set) →
  (bundle : Synthesis.ExperimentBundle World) →
  Synthesis.Observation bundle →
  World → Set
RefineByBundle compatible bundle outcome world =
  compatible world × Synthesis.observe bundle world ≡ outcome

------------------------------------------------------------------------
-- Observation-dependent experiment tree.
------------------------------------------------------------------------

data SequentialConsumerPlan
    (consumer : World → Prediction) :
    (World → Set) → Set₁ where
  closeConsumer :
    ∀ {compatible} →
    Envelope.PointIdentifiable (λ (_ : ⊤) world → compatible world)
      consumer tt →
    SequentialConsumerPlan consumer compatible

  askThen :
    ∀ {compatible}
      (bundle : Synthesis.ExperimentBundle World) →
      ((outcome : Synthesis.Observation bundle) →
        SequentialConsumerPlan consumer
          (RefineByBundle compatible bundle outcome)) →
    SequentialConsumerPlan consumer compatible

------------------------------------------------------------------------
-- The terminal constructor really closes exactly the requested consumer.
------------------------------------------------------------------------

terminalConsumerIdentifiable :
  ∀ {consumer : World → Prediction}
    {compatible : World → Set}
    (identifiable :
      Envelope.PointIdentifiable (λ (_ : ⊤) world → compatible world)
        consumer tt) →
  SequentialConsumerPlan consumer compatible
terminalConsumerIdentifiable = closeConsumer

------------------------------------------------------------------------
-- Worst-case cumulative cost certificate.
--
-- `PlanCostAtMost plan budget` is proof-relevant.  At a branching experiment,
-- every possible outcome branch must fit under the declared total bound.
------------------------------------------------------------------------

data PlanCostAtMost
    {consumer : World → Prediction}
    {compatible : World → Set} :
    SequentialConsumerPlan consumer compatible → Nat → Set₁ where
  closeCost :
    ∀ {identifiable budget} →
    zero ≤ budget →
    PlanCostAtMost (closeConsumer identifiable) budget

  askCost :
    ∀ {bundle continuations budget}
      (branchBudget : Synthesis.Observation bundle → Nat) →
      ((outcome : Synthesis.Observation bundle) →
        PlanCostAtMost (continuations outcome) (branchBudget outcome)) →
      ((outcome : Synthesis.Observation bundle) →
        Synthesis.cost bundle + branchBudget outcome ≤ budget) →
    PlanCostAtMost (askThen bundle continuations) budget

------------------------------------------------------------------------
-- Minimality compares certified worst-case bounds over an application-declared
-- plan library.  This is minimax resource cost, not a probability-weighted
-- expected cost and not scientific truth.
------------------------------------------------------------------------

record CertifiedSequentialPlan
    (consumer : World → Prediction)
    (compatible : World → Set) : Set₂ where
  constructor certifiedSequentialPlan
  field
    plan : SequentialConsumerPlan consumer compatible
    worstCaseCostBound : Nat
    costCertificate : PlanCostAtMost plan worstCaseCostBound
    planReference : String

open CertifiedSequentialPlan public

record MinimalSequentialConsumerPlan
    (consumer : World → Prediction)
    (compatible : World → Set)
    (Declared : CertifiedSequentialPlan consumer compatible → Set) : Set₂ where
  constructor minimalSequentialConsumerPlan
  field
    selected : CertifiedSequentialPlan consumer compatible
    selectedDeclared : Declared selected
    minimalWorstCaseCost :
      (alternative : CertifiedSequentialPlan consumer compatible) →
      Declared alternative →
      worstCaseCostBound selected ≤ worstCaseCostBound alternative
    comparisonReference : String

open MinimalSequentialConsumerPlan public

------------------------------------------------------------------------
-- One-shot prospective closure embeds into the sequential language as a tree
-- of depth one: ask the bundle, then close on every possible outcome.
------------------------------------------------------------------------

oneShotConsumerClosingPlan :
  ∀ {Evidence : Set}
    (compatible : Envelope.Compatible Evidence World)
    (consumer : World → Prediction)
    (evidence : Evidence)
    (bundle : Synthesis.ExperimentBundle World) →
  Synthesis.ProspectivelyClosesConsumer compatible consumer bundle →
  SequentialConsumerPlan consumer (compatible evidence)
oneShotConsumerClosingPlan compatible consumer evidence bundle closes =
  askThen bundle λ outcome →
    closeConsumer (closes evidenceWitness compatibilityWitness)
  where
    evidenceWitness : World
    evidenceWitness = ?

    compatibilityWitness : compatible evidence evidenceWitness
    compatibilityWitness = ?

------------------------------------------------------------------------
-- The generic one-shot embedding above cannot choose a true world from mere
-- evidence.  The honest executable embedding therefore takes the witnessed
-- current state explicitly.  This is the form applications should use.
------------------------------------------------------------------------

oneShotConsumerClosingPlanFromWitness :
  ∀ {Evidence : Set}
    (compatible : Envelope.Compatible Evidence World)
    (consumer : World → Prediction)
    (evidence : Evidence)
    (witness : World) →
    compatible evidence witness →
    (bundle : Synthesis.ExperimentBundle World) →
    Synthesis.ProspectivelyClosesConsumer compatible consumer bundle →
  SequentialConsumerPlan consumer (compatible evidence)
oneShotConsumerClosingPlanFromWitness
    compatible consumer evidence witness witnessCompatible bundle closes =
  askThen bundle λ outcome →
    closeConsumer
      (record
        { unique = λ left right leftCompatible rightCompatible →
            Envelope.PointIdentifiable.unique
              (closes evidence witness witnessCompatible)
              left right
              (proj₁ leftCompatible , proj₂ leftCompatible)
              (proj₁ rightCompatible , proj₂ rightCompatible)
        })

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SequentialExperimentPlannerBoundary : Set where
  constructor sequentialExperimentPlannerBoundary
  field
    oneExperimentMustCloseEveryConsumer : Bool
    oneExperimentMustCloseEveryConsumerIsFalse :
      oneExperimentMustCloseEveryConsumer ≡ false

    nextExperimentMayDependOnObservedOutcome : Bool
    nextExperimentMayDependOnObservedOutcomeIsTrue :
      nextExperimentMayDependOnObservedOutcome ≡ true

    terminalConsumerClosureRequiresFullWorldIdentity : Bool
    terminalConsumerClosureRequiresFullWorldIdentityIsFalse :
      terminalConsumerClosureRequiresFullWorldIdentity ≡ false

    worstCaseCostIsProbabilityWeightedExpectedCost : Bool
    worstCaseCostIsProbabilityWeightedExpectedCostIsFalse :
      worstCaseCostIsProbabilityWeightedExpectedCost ≡ false

canonicalSequentialExperimentPlannerBoundary : SequentialExperimentPlannerBoundary
canonicalSequentialExperimentPlannerBoundary =
  sequentialExperimentPlannerBoundary
    false refl true refl false refl false refl
