module DASHI.Biology.CausalEstimatorFiniteProbabilityConsistencyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Biology.CausalEstimatorGuaranteesExact as Guarantees

------------------------------------------------------------------------
-- FINITE-LAW CONVERGENCE IN PROBABILITY
--
-- No sigma-algebra or general measure space is introduced here.  For an
-- indexed family of already-normalized finite estimator sampling laws, classify
-- every sample atom as inside/outside an estimator-target radius, sum exactly
-- the probability mass of the outside atoms, and reuse the existing generic
-- metric convergence kernel to require that outside mass -> 0.
------------------------------------------------------------------------

outsideContribution : Bool → ℚ → ℚ
outsideContribution false mass = 0ℚ
outsideContribution true mass = mass

finiteOutsideMass :
  ∀ {estimand}
    {procedure : Statistical.EstimatorProcedure estimand} →
  (isOutside : Guarantees.WeightedEstimatorSample procedure → Bool) →
  List (Guarantees.WeightedEstimatorSample procedure) → ℚ
finiteOutsideMass isOutside [] = 0ℚ
finiteOutsideMass isOutside (atom ∷ atoms) =
  outsideContribution (isOutside atom) (Guarantees.sampleMass atom)
  + finiteOutsideMass isOutside atoms

record FiniteProbabilityConsistencySurface
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor finite-probability-consistency-surface
  field
    Index Radius Value MassTolerance : Set

    _≼_ : Index → Index → Set
    PositiveRadius : Radius → Set
    PositiveMassTolerance : MassTolerance → Set

    estimateToValue : Statistical.Estimate procedure → Value
    targetValue : Value
    CloseEstimate : Value → Value → Radius → Set

    samplingLawAt :
      Index → Guarantees.NormalizedFiniteEstimatorSamplingLaw procedure

    outsideDecision :
      (index : Index) →
      (radius : Radius) →
      Guarantees.WeightedEstimatorSample procedure → Bool

    outsideTrueMeansNotClose :
      (index : Index) →
      (radius : Radius) →
      (atom : Guarantees.WeightedEstimatorSample procedure) →
      outsideDecision index radius atom ≡ true →
      ¬ CloseEstimate
          (estimateToValue
            (Statistical.estimator procedure (Guarantees.sample atom)))
          targetValue radius

    outsideFalseMeansClose :
      (index : Index) →
      (radius : Radius) →
      (atom : Guarantees.WeightedEstimatorSample procedure) →
      outsideDecision index radius atom ≡ false →
      CloseEstimate
        (estimateToValue
          (Statistical.estimator procedure (Guarantees.sample atom)))
        targetValue radius

    MassClose : ℚ → ℚ → MassTolerance → Set

    indexReference : String
    estimatorMetricReference : String
    finiteSamplingReference : String
    outsideDecisionReference : String
    massMetricReference : String

open FiniteProbabilityConsistencySurface public

outsideMassAt :
  ∀ {estimand procedure}
    (surface : FiniteProbabilityConsistencySurface
      {estimand} procedure) →
  Index surface → Radius surface → ℚ
outsideMassAt surface index radius =
  finiteOutsideMass
    (outsideDecision surface index radius)
    (Guarantees.atoms (samplingLawAt surface index))

------------------------------------------------------------------------
-- The outer metric problem is on probability mass itself.  Radius is a
-- parameter: for every estimator radius, the outside probability mass must
-- approach zero as the sampling index grows.
------------------------------------------------------------------------

asOutsideMassLimitProblem :
  ∀ {estimand procedure} →
  FiniteProbabilityConsistencySurface {estimand} procedure →
  Metric.ParameterisedMetricLimitProblem
asOutsideMassLimitProblem surface = record
  { Parameter = Radius surface
  ; Index = Index surface
  ; Value = ℚ
  ; Epsilon = MassTolerance surface
  ; _≼_ = _≼_ surface
  ; Positive = PositiveMassTolerance surface
  ; Close = MassClose surface
  ; family = λ radius index → outsideMassAt surface index radius
  ; candidate = λ _ → 0ℚ
  ; reading =
      "For each estimator-target radius, exact outside mass of the finite normalized sampling law converges to zero."
  }

record FiniteLawConvergenceInProbability
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand)
    (surface : FiniteProbabilityConsistencySurface procedure) : Set₁ where
  constructor finite-law-convergence-in-probability
  field
    outsideMassConvergesToZero :
      Metric.PointwiseMetricConvergence (asOutsideMassLimitProblem surface)

    sameEstimatorTarget : Set
    sameEstimatorTargetReceipt : sameEstimatorTarget

    convergenceReference : String
    targetWeldReference : String

open FiniteLawConvergenceInProbability public

finiteProbabilityTail :
  ∀ {estimand procedure surface}
    (guarantee : FiniteLawConvergenceInProbability
      {estimand} procedure surface) →
  (radius : Radius surface) →
  (massTolerance : MassTolerance surface) →
  PositiveMassTolerance surface massTolerance →
  (index : Index surface) →
  _≼_ surface
    (Metric.threshold
      (outsideMassConvergesToZero guarantee)
      radius massTolerance)
    index →
  MassClose surface
    (outsideMassAt surface index radius)
    0ℚ
    massTolerance
finiteProbabilityTail guarantee radius massTolerance positive index afterThreshold =
  Metric.tailClose
    (outsideMassConvergesToZero guarantee)
    radius
    massTolerance
    positive
    index
    afterThreshold

------------------------------------------------------------------------
-- Boundary: this is a genuine finite-law analogue of convergence in
-- probability, but it does not manufacture a general measure-theoretic
-- probability space or any distributional/normal limit theorem.
------------------------------------------------------------------------

data FiniteProbabilityConsistencyMeansGeneralMeasurePermission : Set where

data FiniteProbabilityConsistencyMeansWeakConvergencePermission : Set where

data FiniteProbabilityConsistencyMeansAsymptoticNormalityPermission : Set where

data MetricConsistencyMeansFiniteProbabilityConsistencyPermission : Set where

data FiniteProbabilityConsistencyMeansUnbiasedPermission : Set where

data FiniteProbabilityConsistencyMeansRepresentativeSamplingPermission : Set where

finiteProbabilityConsistencyDoesNotCreateGeneralMeasure :
  FiniteProbabilityConsistencyMeansGeneralMeasurePermission → ⊥
finiteProbabilityConsistencyDoesNotCreateGeneralMeasure ()

finiteProbabilityConsistencyDoesNotCreateWeakConvergence :
  FiniteProbabilityConsistencyMeansWeakConvergencePermission → ⊥
finiteProbabilityConsistencyDoesNotCreateWeakConvergence ()

finiteProbabilityConsistencyDoesNotCreateAsymptoticNormality :
  FiniteProbabilityConsistencyMeansAsymptoticNormalityPermission → ⊥
finiteProbabilityConsistencyDoesNotCreateAsymptoticNormality ()

metricConsistencyDoesNotAutomaticallyPayFiniteProbabilityConsistency :
  MetricConsistencyMeansFiniteProbabilityConsistencyPermission → ⊥
metricConsistencyDoesNotAutomaticallyPayFiniteProbabilityConsistency ()

finiteProbabilityConsistencyDoesNotCreateUnbiasedness :
  FiniteProbabilityConsistencyMeansUnbiasedPermission → ⊥
finiteProbabilityConsistencyDoesNotCreateUnbiasedness ()

finiteProbabilityConsistencyDoesNotProveRepresentativeSampling :
  FiniteProbabilityConsistencyMeansRepresentativeSamplingPermission → ⊥
finiteProbabilityConsistencyDoesNotProveRepresentativeSampling ()

record CausalEstimatorFiniteProbabilityConsistencyBoundary : Set where
  constructor causal-estimator-finite-probability-consistency-boundary
  field
    normalizedFiniteSamplingLawReused : Bool
    outsideEventMassComputedExactly : Bool
    outsideMassLimitUsesExistingMetricKernel : Bool
    finiteLawProbabilityConsistencyAvailable : Bool
    generalMeasureSpaceInventedHere : Bool
    weakConvergenceInventedHere : Bool
    asymptoticNormalityInventedHere : Bool

canonicalCausalEstimatorFiniteProbabilityConsistencyBoundary :
  CausalEstimatorFiniteProbabilityConsistencyBoundary
canonicalCausalEstimatorFiniteProbabilityConsistencyBoundary =
  causal-estimator-finite-probability-consistency-boundary
    true true true true false false false
