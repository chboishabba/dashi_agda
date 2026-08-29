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
-- consumer.  The next experiment may therefore depend on the realised outcome,
-- with the compatible-state fibre refined along that branch.
--
-- Terminal success is consumer point-identifiability, not full hidden-world
-- identity.  No probability model is assumed.  Cost certificates below are
-- worst-case bounds over all outcomes that are actually compatible with the
-- current fibre.
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

OutcomePossible :
  (compatible : World → Set) →
  (bundle : Synthesis.ExperimentBundle World) →
  Synthesis.Observation bundle → Set
OutcomePossible compatible bundle outcome =
  Σ World λ world → RefineByBundle compatible bundle outcome world

------------------------------------------------------------------------
-- Observation-dependent experiment tree.  Impossible measurement outcomes do
-- not generate proof obligations; every compatible/realizable branch does.
------------------------------------------------------------------------

data SequentialConsumerPlan
    (consumer : World → Prediction) :
    (World → Set) → Set₁ where
  closeConsumer :
    ∀ {compatible} →
    (∀ left right →
      compatible left →
      compatible right →
      consumer left ≡ consumer right) →
    SequentialConsumerPlan consumer compatible

  askThen :
    ∀ {compatible}
      (bundle : Synthesis.ExperimentBundle World) →
      ((outcome : Synthesis.Observation bundle) →
        OutcomePossible compatible bundle outcome →
        SequentialConsumerPlan consumer
          (RefineByBundle compatible bundle outcome)) →
    SequentialConsumerPlan consumer compatible

terminalConsumerIdentifiable :
  ∀ {consumer : World → Prediction}
    {compatible : World → Set} →
  (∀ left right →
    compatible left →
    compatible right →
    consumer left ≡ consumer right) →
  SequentialConsumerPlan consumer compatible
terminalConsumerIdentifiable = closeConsumer

------------------------------------------------------------------------
-- Worst-case cumulative cost.  Every realizable outcome branch must stay under
-- the common declared total budget.
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
        (possible : OutcomePossible compatible bundle outcome) →
        PlanCostAtMost
          (continuations outcome possible)
          (branchBudget outcome)) →
      ((outcome : Synthesis.Observation bundle) →
        OutcomePossible compatible bundle outcome →
        Synthesis.cost bundle + branchBudget outcome ≤ budget) →
    PlanCostAtMost (askThen bundle continuations) budget

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
-- A one-shot prospectively consumer-closing bundle is a depth-one sequential
-- plan.  The branch's realizability witness supplies exactly the true state
-- needed by the existing Stage-6 prospective-closure theorem.
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
  askThen bundle λ outcome possible →
    closeConsumer λ left right leftCompatible rightCompatible →
      closes
        evidence
        (proj₁ possible)
        (proj₁ (proj₂ possible))
        left right leftCompatible rightCompatible

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

    impossibleOutcomeCreatesContinuationObligation : Bool
    impossibleOutcomeCreatesContinuationObligationIsFalse :
      impossibleOutcomeCreatesContinuationObligation ≡ false

    terminalConsumerClosureRequiresFullWorldIdentity : Bool
    terminalConsumerClosureRequiresFullWorldIdentityIsFalse :
      terminalConsumerClosureRequiresFullWorldIdentity ≡ false

    worstCaseCostIsProbabilityWeightedExpectedCost : Bool
    worstCaseCostIsProbabilityWeightedExpectedCostIsFalse :
      worstCaseCostIsProbabilityWeightedExpectedCost ≡ false

canonicalSequentialExperimentPlannerBoundary : SequentialExperimentPlannerBoundary
canonicalSequentialExperimentPlannerBoundary =
  sequentialExperimentPlannerBoundary
    false refl true refl false refl false refl false refl
