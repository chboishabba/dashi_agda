module DASHI.Core.SequentialConsumerExperimentPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis

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

oneShotContinuation :
  ∀ {Evidence : Set}
    (compatible : Envelope.Compatible Evidence World)
    (consumer : World → Prediction)
    (evidence : Evidence)
    (bundle : Synthesis.ExperimentBundle World)
    (closes : Synthesis.ProspectivelyClosesConsumer compatible consumer bundle)
    (outcome : Synthesis.Observation bundle) →
    OutcomePossible (compatible evidence) bundle outcome →
    SequentialConsumerPlan consumer
      (RefineByBundle (compatible evidence) bundle outcome)
oneShotContinuation compatible consumer evidence bundle closes outcome possible =
  closeConsumer λ left right leftCompatible rightCompatible →
    closure
      left right
      (proj₁ leftCompatible ,
        trans (proj₂ leftCompatible) (sym realisedOutcome))
      (proj₁ rightCompatible ,
        trans (proj₂ rightCompatible) (sym realisedOutcome))
  where
    witness : World
    witness = proj₁ possible

    witnessCompatible : compatible evidence witness
    witnessCompatible = proj₁ (proj₂ possible)

    realisedOutcome : Synthesis.observe bundle witness ≡ outcome
    realisedOutcome = proj₂ (proj₂ possible)

    closure :
      Envelope.MeasurementClosesEnvelope
        compatible
        (Synthesis.observe bundle)
        consumer
        (evidence , Synthesis.observe bundle witness)
    closure = closes evidence witness witnessCompatible

oneShotConsumerClosingPlan :
  ∀ {Evidence : Set}
    (compatible : Envelope.Compatible Evidence World)
    (consumer : World → Prediction)
    (evidence : Evidence)
    (bundle : Synthesis.ExperimentBundle World) →
  Synthesis.ProspectivelyClosesConsumer compatible consumer bundle →
  SequentialConsumerPlan consumer (compatible evidence)
oneShotConsumerClosingPlan compatible consumer evidence bundle closes =
  askThen bundle (oneShotContinuation compatible consumer evidence bundle closes)

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
