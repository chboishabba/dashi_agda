module DASHI.Core.SequentialRobustActionabilityPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust

------------------------------------------------------------------------
-- SEQUENTIAL INFORMATION -> ROBUST AUTHORISED ACTION
--
-- The previous experiment planner terminates when a declared prediction or
-- decision consumer becomes point-identifiable.  This sibling planner stops
-- even earlier when the live hypothesis fibre already supports one intervention
-- that is robust relative to the baseline AND independently authorised.
--
-- Thus full model identification is not required before action, while robust
-- support alone still cannot manufacture authority.
------------------------------------------------------------------------

private
  variable
    Hypothesis Intervention Outcome : Set

RefineHypotheses :
  (live : Hypothesis → Set) →
  (bundle : Synthesis.ExperimentBundle Hypothesis) →
  Synthesis.Observation bundle →
  Hypothesis → Set
RefineHypotheses live bundle observed hypothesis =
  live hypothesis × Synthesis.observe bundle hypothesis ≡ observed

HypothesisOutcomePossible :
  (live : Hypothesis → Set) →
  (bundle : Synthesis.ExperimentBundle Hypothesis) →
  Synthesis.Observation bundle → Set
HypothesisOutcomePossible live bundle observed =
  Σ Hypothesis λ hypothesis → RefineHypotheses live bundle observed hypothesis

------------------------------------------------------------------------
-- Outcome-adaptive plan.  `Authority` is application supplied and deliberately
-- separate from robustness.
------------------------------------------------------------------------

data SequentialActionabilityPlan
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set) :
    (Hypothesis → Set) → Set₁ where

  actNow :
    ∀ {live}
      (intervention : Intervention) →
      Robust.RobustlyNoWorseThanBaseline system live intervention →
      Authority intervention →
    SequentialActionabilityPlan system Authority live

  measureThen :
    ∀ {live}
      (bundle : Synthesis.ExperimentBundle Hypothesis) →
      ((observed : Synthesis.Observation bundle) →
        HypothesisOutcomePossible live bundle observed →
        SequentialActionabilityPlan
          system Authority
          (RefineHypotheses live bundle observed)) →
    SequentialActionabilityPlan system Authority live

------------------------------------------------------------------------
-- Refinement preserves an already available robust action, so information is
-- unnecessary for robustness itself once `actNow` is inhabited.  An application
-- may still choose to measure for a different consumer, but not because this
-- robustness proof demands it.
------------------------------------------------------------------------

robustActionSurvivesMeasuredRefinement :
  ∀ {system : Robust.HypothesisInterventionSystem
        Hypothesis Intervention Outcome}
    {live : Hypothesis → Set}
    {intervention : Intervention}
    (robust : Robust.RobustlyNoWorseThanBaseline system live intervention)
    (bundle : Synthesis.ExperimentBundle Hypothesis)
    (observed : Synthesis.Observation bundle) →
  Robust.RobustlyNoWorseThanBaseline
    system
    (RefineHypotheses live bundle observed)
    intervention
robustActionSurvivesMeasuredRefinement robust bundle observed =
  Robust.robustnessSurvivesHypothesisRefinement
    (λ hypothesis refined → proj₁ refined)
    robust

------------------------------------------------------------------------
-- Worst-case resource bound over every realizable information branch.
------------------------------------------------------------------------

data ActionabilityPlanCostAtMost
    {system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome}
    {Authority : Intervention → Set}
    {live : Hypothesis → Set} :
    SequentialActionabilityPlan system Authority live → Nat → Set₁ where

  actCost :
    ∀ {intervention robust authority budget} →
    zero ≤ budget →
    ActionabilityPlanCostAtMost
      (actNow intervention robust authority)
      budget

  measureCost :
    ∀ {bundle continuations budget}
      (branchBudget : Synthesis.Observation bundle → Nat) →
      ((observed : Synthesis.Observation bundle) →
        (possible : HypothesisOutcomePossible live bundle observed) →
        ActionabilityPlanCostAtMost
          (continuations observed possible)
          (branchBudget observed)) →
      ((observed : Synthesis.Observation bundle) →
        HypothesisOutcomePossible live bundle observed →
        Synthesis.cost bundle + branchBudget observed ≤ budget) →
    ActionabilityPlanCostAtMost
      (measureThen bundle continuations)
      budget

record CertifiedSequentialActionabilityPlan
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (live : Hypothesis → Set) : Set₂ where
  constructor certifiedSequentialActionabilityPlan
  field
    plan : SequentialActionabilityPlan system Authority live
    worstCaseCostBound : Nat
    costCertificate : ActionabilityPlanCostAtMost plan worstCaseCostBound
    planReference : String

open CertifiedSequentialActionabilityPlan public

record MinimalSequentialActionabilityPlan
    (system : Robust.HypothesisInterventionSystem
      Hypothesis Intervention Outcome)
    (Authority : Intervention → Set)
    (live : Hypothesis → Set)
    (Declared : CertifiedSequentialActionabilityPlan system Authority live → Set)
    : Set₂ where
  constructor minimalSequentialActionabilityPlan
  field
    selected : CertifiedSequentialActionabilityPlan system Authority live
    selectedDeclared : Declared selected
    minimalWorstCaseCost :
      (alternative : CertifiedSequentialActionabilityPlan system Authority live) →
      Declared alternative →
      worstCaseCostBound selected ≤ worstCaseCostBound alternative
    comparisonReference : String

open MinimalSequentialActionabilityPlan public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SequentialActionabilityPlannerBoundary : Set where
  constructor sequentialActionabilityPlannerBoundary
  field
    fullHypothesisIdentificationRequiredBeforeEveryAction : Bool
    fullHypothesisIdentificationRequiredBeforeEveryActionIsFalse :
      fullHypothesisIdentificationRequiredBeforeEveryAction ≡ false

    robustSupportAutomaticallyCreatesAuthority : Bool
    robustSupportAutomaticallyCreatesAuthorityIsFalse :
      robustSupportAutomaticallyCreatesAuthority ≡ false

    realisedMeasurementMaySelectDifferentNextExperiment : Bool
    realisedMeasurementMaySelectDifferentNextExperimentIsTrue :
      realisedMeasurementMaySelectDifferentNextExperiment ≡ true

    informationCanBeSkippedWhenRobustAuthorisedActionAlreadyExists : Bool
    informationCanBeSkippedWhenRobustAuthorisedActionAlreadyExistsIsTrue :
      informationCanBeSkippedWhenRobustAuthorisedActionAlreadyExists ≡ true

canonicalSequentialActionabilityPlannerBoundary :
  SequentialActionabilityPlannerBoundary
canonicalSequentialActionabilityPlannerBoundary =
  sequentialActionabilityPlannerBoundary
    false refl false refl true refl true refl
