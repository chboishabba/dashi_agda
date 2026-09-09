module DASHI.Biology.CausalEstimatorFiniteTestDistributionConvergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Biology.CausalEstimatorGuaranteesExact as Guarantees
import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected

record WeightedTargetValue (Value : Set) : Set where
  constructor weighted-target-value
  field
    probability : Expected.ProbabilityAtom
    value : Value

open WeightedTargetValue public

targetMass : ∀ {Value} → WeightedTargetValue Value → ℚ
targetMass atom = Expected.probabilityMass (probability atom)

finiteTargetMass : ∀ {Value} → List (WeightedTargetValue Value) → ℚ
finiteTargetMass [] = 0ℚ
finiteTargetMass (atom ∷ atoms) = targetMass atom + finiteTargetMass atoms

record NormalizedFiniteTargetLaw (Value : Set) : Set₁ where
  constructor normalized-finite-target-law
  field
    atoms : List (WeightedTargetValue Value)
    normalized : finiteTargetMass atoms ≡ 1ℚ
    targetLawReference : String

open NormalizedFiniteTargetLaw public

finiteEstimatorTestExpectation :
  ∀ {estimand}
    {procedure : Statistical.EstimatorProcedure estimand}
    {Test Value : Set} →
  (estimateToValue : Statistical.Estimate procedure → Value) →
  (test : Test → Value → ℚ) →
  Test →
  List (Guarantees.WeightedEstimatorSample procedure) → ℚ
finiteEstimatorTestExpectation estimateToValue test selected [] = 0ℚ
finiteEstimatorTestExpectation {procedure = procedure}
  estimateToValue test selected (atom ∷ atoms) =
  Guarantees.sampleMass atom
    * test selected
        (estimateToValue
          (Statistical.estimator procedure (Guarantees.sample atom)))
  + finiteEstimatorTestExpectation estimateToValue test selected atoms

finiteTargetTestExpectation :
  ∀ {Test Value : Set} →
  (test : Test → Value → ℚ) →
  Test → List (WeightedTargetValue Value) → ℚ
finiteTargetTestExpectation test selected [] = 0ℚ
finiteTargetTestExpectation test selected (atom ∷ atoms) =
  targetMass atom * test selected (value atom)
  + finiteTargetTestExpectation test selected atoms

record FiniteTestDistributionSurface
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor finite-test-distribution-surface
  field
    Index Test Value Tolerance : Set
    _≼_ : Index → Index → Set
    PositiveTolerance : Tolerance → Set

    estimateToValue : Statistical.Estimate procedure → Value
    testFunction : Test → Value → ℚ

    samplingLawAt :
      Index → Guarantees.NormalizedFiniteEstimatorSamplingLaw procedure
    targetLaw : NormalizedFiniteTargetLaw Value

    ExpectationClose : ℚ → ℚ → Tolerance → Set

    indexReference : String
    testClassReference : String
    estimatorLawReference : String
    targetLawReference : String
    expectationMetricReference : String

open FiniteTestDistributionSurface public

estimatorExpectationAt :
  ∀ {estimand procedure}
    (surface : FiniteTestDistributionSurface {estimand} procedure) →
  Test surface → Index surface → ℚ
estimatorExpectationAt surface test index =
  finiteEstimatorTestExpectation
    (estimateToValue surface)
    (testFunction surface)
    test
    (Guarantees.atoms (samplingLawAt surface index))

targetExpectationAt :
  ∀ {estimand procedure}
    (surface : FiniteTestDistributionSurface {estimand} procedure) →
  Test surface → ℚ
targetExpectationAt surface test =
  finiteTargetTestExpectation
    (testFunction surface)
    test
    (atoms (targetLaw surface))

asTestExpectationLimitProblem :
  ∀ {estimand procedure} →
  FiniteTestDistributionSurface {estimand} procedure →
  Metric.ParameterisedMetricLimitProblem
asTestExpectationLimitProblem surface = record
  { Parameter = Test surface
  ; Index = Index surface
  ; Value = ℚ
  ; Epsilon = Tolerance surface
  ; _≼_ = _≼_ surface
  ; Positive = PositiveTolerance surface
  ; Close = ExpectationClose surface
  ; family = estimatorExpectationAt surface
  ; candidate = targetExpectationAt surface
  ; reading =
      "Exact finite expectations of every declared test function converge to the corresponding finite target-law expectation."
  }

record FiniteTestFunctionDistributionConvergence
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand)
    (surface : FiniteTestDistributionSurface procedure) : Set₁ where
  constructor finite-test-function-distribution-convergence
  field
    testExpectationConvergence :
      Metric.PointwiseMetricConvergence
        (asTestExpectationLimitProblem surface)

    testClassDeterminesIntendedDistribution : Set
    testClassAdequacyReceipt : testClassDeterminesIntendedDistribution

    convergenceReference : String
    adequacyReference : String

open FiniteTestFunctionDistributionConvergence public

finiteTestDistributionTail :
  ∀ {estimand procedure surface}
    (convergence : FiniteTestFunctionDistributionConvergence
      {estimand} procedure surface) →
  (test : Test surface) →
  (tolerance : Tolerance surface) →
  PositiveTolerance surface tolerance →
  (index : Index surface) →
  _≼_ surface
    (Metric.threshold
      (testExpectationConvergence convergence)
      test tolerance)
    index →
  ExpectationClose surface
    (estimatorExpectationAt surface test index)
    (targetExpectationAt surface test)
    tolerance
finiteTestDistributionTail convergence test tolerance positive index afterThreshold =
  Metric.tailClose
    (testExpectationConvergence convergence)
    test tolerance positive index afterThreshold

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteTestsMeanGeneralWeakConvergencePermission : Set where

data FiniteTargetLawMeansNormalDistributionPermission : Set where

data TestClassAdequacyIsAutomaticPermission : Set where

data DistributionConvergenceMeansAsymptoticNormalityPermission : Set where

data DistributionConvergenceMeansCausalIdentificationPermission : Set where

finiteTestsDoNotCreateGeneralWeakConvergence :
  FiniteTestsMeanGeneralWeakConvergencePermission → ⊥
finiteTestsDoNotCreateGeneralWeakConvergence ()

finiteTargetLawDoesNotBecomeNormalDistribution :
  FiniteTargetLawMeansNormalDistributionPermission → ⊥
finiteTargetLawDoesNotBecomeNormalDistribution ()

testClassAdequacyIsNotAutomatic :
  TestClassAdequacyIsAutomaticPermission → ⊥
testClassAdequacyIsNotAutomatic ()

finiteDistributionConvergenceDoesNotCreateAsymptoticNormality :
  DistributionConvergenceMeansAsymptoticNormalityPermission → ⊥
finiteDistributionConvergenceDoesNotCreateAsymptoticNormality ()

finiteDistributionConvergenceDoesNotIdentifyCause :
  DistributionConvergenceMeansCausalIdentificationPermission → ⊥
finiteDistributionConvergenceDoesNotIdentifyCause ()

record CausalEstimatorFiniteTestDistributionBoundary : Set where
  constructor causal-estimator-finite-test-distribution-boundary
  field
    finiteEstimatorLawReused : Bool
    finiteTargetLawExplicit : Bool
    exactTestExpectationsComputed : Bool
    testExpectationConvergenceUsesMetricKernel : Bool
    testClassAdequacyPaidSeparately : Bool
    generalWeakConvergenceInventedHere : Bool
    normalLimitInventedHere : Bool

canonicalCausalEstimatorFiniteTestDistributionBoundary :
  CausalEstimatorFiniteTestDistributionBoundary
canonicalCausalEstimatorFiniteTestDistributionBoundary =
  causal-estimator-finite-test-distribution-boundary
    true true true true true false false
