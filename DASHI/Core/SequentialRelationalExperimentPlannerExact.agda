module DASHI.Core.SequentialRelationalExperimentPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

------------------------------------------------------------------------
-- SEQUENTIAL PLANNING FOR SET-VALUED / RELATIONAL PREDICTIONS
--
-- Deterministic sensors fit `SequentialConsumerExperimentPlannerExact`.  In
-- fundamental physics and many uncertain models a hypothesis may admit several
-- outcomes.  This sibling calculus refines a live hypothesis fibre by the
-- relation `predicts hypothesis experiment observed` rather than by equality to
-- one deterministic readout.
------------------------------------------------------------------------

record RelationalExperimentSystem
    (Hypothesis Experiment Observation : Set) : Set₁ where
  constructor relationalExperimentSystem
  field
    predicts : Hypothesis → Experiment → Observation → Set
    experimentCost : Experiment → Nat
    experimentReference : Experiment → String
    observationClassificationReference : Observation → String

open RelationalExperimentSystem public

private
  variable
    Hypothesis Experiment Observation Consumer : Set

RefineByOutcome :
  (system : RelationalExperimentSystem Hypothesis Experiment Observation) →
  (live : Hypothesis → Set) →
  Experiment → Observation → Hypothesis → Set
RefineByOutcome system live experiment observed hypothesis =
  live hypothesis × predicts system hypothesis experiment observed

RelationalOutcomePossible :
  (system : RelationalExperimentSystem Hypothesis Experiment Observation) →
  (live : Hypothesis → Set) →
  Experiment → Observation → Set
RelationalOutcomePossible system live experiment observed =
  Σ Hypothesis λ hypothesis →
    RefineByOutcome system live experiment observed hypothesis

------------------------------------------------------------------------
-- Tree terminates when the requested consumer is constant on the live theory
-- fibre.  That consumer may be theory identity, a prediction, a decision class,
-- or any application-supplied quotient.
------------------------------------------------------------------------

data SequentialRelationalPlan
    (system : RelationalExperimentSystem Hypothesis Experiment Observation)
    (consumer : Hypothesis → Consumer) :
    (Hypothesis → Set) → Set₁ where

  closeRelationalConsumer :
    ∀ {live} →
    (∀ left right →
      live left → live right →
      consumer left ≡ consumer right) →
    SequentialRelationalPlan system consumer live

  runThen :
    ∀ {live}
      (experiment : Experiment) →
      ((observed : Observation) →
        RelationalOutcomePossible system live experiment observed →
        SequentialRelationalPlan
          system consumer
          (RefineByOutcome system live experiment observed)) →
    SequentialRelationalPlan system consumer live

------------------------------------------------------------------------
-- Worst-case cumulative experiment cost over realizable branches.
------------------------------------------------------------------------

data RelationalPlanCostAtMost
    {system : RelationalExperimentSystem Hypothesis Experiment Observation}
    {consumer : Hypothesis → Consumer}
    {live : Hypothesis → Set} :
    SequentialRelationalPlan system consumer live → Nat → Set₁ where

  closeCost :
    ∀ {identifiable budget} →
    zero ≤ budget →
    RelationalPlanCostAtMost
      (closeRelationalConsumer identifiable)
      budget

  runCost :
    ∀ {experiment continuations budget}
      (branchBudget : Observation → Nat) →
      ((observed : Observation) →
        (possible : RelationalOutcomePossible system live experiment observed) →
        RelationalPlanCostAtMost
          (continuations observed possible)
          (branchBudget observed)) →
      ((observed : Observation) →
        RelationalOutcomePossible system live experiment observed →
        experimentCost system experiment + branchBudget observed ≤ budget) →
    RelationalPlanCostAtMost
      (runThen experiment continuations)
      budget

record CertifiedSequentialRelationalPlan
    (system : RelationalExperimentSystem Hypothesis Experiment Observation)
    (consumer : Hypothesis → Consumer)
    (live : Hypothesis → Set) : Set₂ where
  constructor certifiedSequentialRelationalPlan
  field
    plan : SequentialRelationalPlan system consumer live
    worstCaseCostBound : Nat
    costCertificate : RelationalPlanCostAtMost plan worstCaseCostBound
    planReference : String

open CertifiedSequentialRelationalPlan public

record MinimalSequentialRelationalPlan
    (system : RelationalExperimentSystem Hypothesis Experiment Observation)
    (consumer : Hypothesis → Consumer)
    (live : Hypothesis → Set)
    (Declared : CertifiedSequentialRelationalPlan system consumer live → Set)
    : Set₂ where
  constructor minimalSequentialRelationalPlan
  field
    selected : CertifiedSequentialRelationalPlan system consumer live
    selectedDeclared : Declared selected
    minimalWorstCaseCost :
      (alternative : CertifiedSequentialRelationalPlan system consumer live) →
      Declared alternative →
      worstCaseCostBound selected ≤ worstCaseCostBound alternative
    comparisonReference : String

open MinimalSequentialRelationalPlan public

record SequentialRelationalPlannerBoundary : Set where
  constructor sequentialRelationalPlannerBoundary
  field
    everyHypothesisMustPredictOneDeterministicOutcome : Bool
    everyHypothesisMustPredictOneDeterministicOutcomeIsFalse :
      everyHypothesisMustPredictOneDeterministicOutcome ≡ false

    overlappingOutcomeSupportCanLeaveHypothesesUnresolved : Bool
    overlappingOutcomeSupportCanLeaveHypothesesUnresolvedIsTrue :
      overlappingOutcomeSupportCanLeaveHypothesesUnresolved ≡ true

    terminalConsumerNeedNotBeFullHypothesisIdentity : Bool
    terminalConsumerNeedNotBeFullHypothesisIdentityIsTrue :
      terminalConsumerNeedNotBeFullHypothesisIdentity ≡ true

canonicalSequentialRelationalPlannerBoundary :
  SequentialRelationalPlannerBoundary
canonicalSequentialRelationalPlannerBoundary =
  sequentialRelationalPlannerBoundary false refl true refl true refl
