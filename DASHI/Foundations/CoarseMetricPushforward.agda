module DASHI.Foundations.CoarseMetricPushforward where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record Projection : Set₁ where
  field
    FineCarrier : Set
    CoarseCarrier : Set
    project : FineCarrier → CoarseCarrier

open Projection public

Fibre :
  (P : Projection) →
  CoarseCarrier P →
  Set
Fibre P coarse =
  Σ (FineCarrier P) (λ fine → project P fine ≡ coarse)

------------------------------------------------------------------------
-- A real-valued or continuous codomain is still an observable codomain.  The
-- fine carrier, projection, and aggregation rule remain explicit.
------------------------------------------------------------------------

record CoarseMetricModel : Set₁ where
  field
    MetricFineState : Set
    MetricCoarseState : Set
    MetricValue : Set

    coarseProjection : MetricFineState → MetricCoarseState
    fineMetric : MetricFineState → MetricFineState → MetricValue
    coarseMetric : MetricCoarseState → MetricCoarseState → MetricValue

    aggregateFibreDistance :
      MetricCoarseState →
      MetricCoarseState →
      MetricValue

    aggregationRuleRecorded : Set

open CoarseMetricModel public

record PushforwardMeasure : Set₁ where
  field
    MeasureFineState : Set
    MeasureCoarseState : Set
    FineEvent : Set
    CoarseEvent : Set
    Measure : Set

    measureProjection : MeasureFineState → MeasureCoarseState
    preimage : CoarseEvent → FineEvent
    fineMass : FineEvent → Measure
    coarseMass : CoarseEvent → Measure

    pushforwardLaw :
      ∀ event →
      coarseMass event ≡ fineMass (preimage event)

open PushforwardMeasure public

record StatisticalObservable : Set₁ where
  field
    ObservedFineState : Set
    Statistic : Set
    statistic : ObservedFineState → Statistic

open StatisticalObservable public

StatisticalFibre :
  (S : StatisticalObservable) →
  Statistic S →
  Set
StatisticalFibre S value =
  Σ (ObservedFineState S) (λ state → statistic S state ≡ value)

------------------------------------------------------------------------
-- Coarse zero mechanisms remain distinct even when one statistic identifies
-- them.  The constructors are structural classifications, not clinical claims.
------------------------------------------------------------------------

data CoarseZeroMechanism : Set where
  fixedZero : CoarseZeroMechanism
  balancedOpposition : CoarseZeroMechanism
  temporalOscillation : CoarseZeroMechanism
  phaseCancellation : CoarseZeroMechanism
  populationMixture : CoarseZeroMechanism
  boundaryDrift : CoarseZeroMechanism

record SameCoarseDifferentFine
    (P : Projection) : Set₁ where
  field
    leftFine rightFine : FineCarrier P
    sharedCoarse : CoarseCarrier P

    leftProjects : project P leftFine ≡ sharedCoarse
    rightProjects : project P rightFine ≡ sharedCoarse
    fineStatesDiffer : leftFine ≢ rightFine

open SameCoarseDifferentFine public

record ResolutionIndexedStatistic : Set₁ where
  field
    Resolution : Set
    Chart : Set
    StatisticValue : Set

    resolution : Resolution
    chart : Chart
    value : StatisticValue

    aggregationWindow : Nat
    aggregationRule : Set

open ResolutionIndexedStatistic public
