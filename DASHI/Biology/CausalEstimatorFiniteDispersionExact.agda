module DASHI.Biology.CausalEstimatorFiniteDispersionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Biology.CausalEstimatorGuaranteesExact as Guarantees
import DASHI.Biology.FiniteRationalCausalEstimandExpectationExact as FiniteTarget

------------------------------------------------------------------------
-- FINITE EXACT DISPERSION / MSE
------------------------------------------------------------------------

squaredDeviation : ℚ → ℚ → ℚ
squaredDeviation x centre = (x - centre) * (x - centre)

finiteExpectedSquaredDeviation :
  ∀ {estimand}
    {procedure : Statistical.EstimatorProcedure estimand} →
  (estimateToRational : Statistical.Estimate procedure → ℚ) →
  List (Guarantees.WeightedEstimatorSample procedure) →
  ℚ → ℚ
finiteExpectedSquaredDeviation estimateToRational [] centre = 0ℚ
finiteExpectedSquaredDeviation {procedure = procedure}
  estimateToRational (atom ∷ atoms) centre =
  Guarantees.sampleMass atom
    * squaredDeviation
        (estimateToRational
          (Statistical.estimator procedure
            (Guarantees.sample atom)))
        centre
  + finiteExpectedSquaredDeviation
      estimateToRational atoms centre

finiteExpectedSquaredDeviationCentreCong :
  ∀ {estimand}
    {procedure : Statistical.EstimatorProcedure estimand}
    (estimateToRational : Statistical.Estimate procedure → ℚ)
    (atoms : List (Guarantees.WeightedEstimatorSample procedure))
    (left right : ℚ) →
  left ≡ right →
  finiteExpectedSquaredDeviation estimateToRational atoms left
  ≡ finiteExpectedSquaredDeviation estimateToRational atoms right
finiteExpectedSquaredDeviationCentreCong estimateToRational atoms left right eq
  rewrite eq = refl

record FiniteRationalEstimatorDispersion
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor finite-rational-estimator-dispersion
  field
    law : Guarantees.NormalizedFiniteEstimatorSamplingLaw procedure
    estimateToRational : Statistical.Estimate procedure → ℚ

    estimatorMean : ℚ
    estimatorMeanIsFiniteExpectation :
      estimatorMean
      ≡ Guarantees.finiteExpectedEstimatorOutput
          procedure estimateToRational (Guarantees.atoms law)

    finiteVariance : ℚ
    finiteVarianceIsSquaredDeviationFromMean :
      finiteVariance
      ≡ finiteExpectedSquaredDeviation
          estimateToRational (Guarantees.atoms law) estimatorMean

open FiniteRationalEstimatorDispersion public

record FiniteRationalEstimatorMSE
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand)
    (dispersion : FiniteRationalEstimatorDispersion procedure) : Set₁ where
  constructor finite-rational-estimator-mse
  field
    target : ℚ

    finiteMSE : ℚ
    finiteMSEIsSquaredDeviationFromTarget :
      finiteMSE
      ≡ finiteExpectedSquaredDeviation
          (estimateToRational dispersion)
          (Guarantees.atoms (law dispersion))
          target

open FiniteRationalEstimatorMSE public

varianceEqualsMSEWhenCentresMatch :
  ∀ {estimand procedure}
    (dispersion : FiniteRationalEstimatorDispersion
      {estimand} procedure)
    (mse : FiniteRationalEstimatorMSE procedure dispersion) →
  estimatorMean dispersion ≡ target mse →
  finiteVariance dispersion ≡ finiteMSE mse
varianceEqualsMSEWhenCentresMatch dispersion mse centresMatch =
  trans
    (finiteVarianceIsSquaredDeviationFromMean dispersion)
    (trans
      (finiteExpectedSquaredDeviationCentreCong
        (estimateToRational dispersion)
        (Guarantees.atoms (law dispersion))
        (estimatorMean dispersion)
        (target mse)
        centresMatch)
      (sym (finiteMSEIsSquaredDeviationFromTarget mse)))

unbiasednessGivesMeanTargetEquality :
  ∀ {scope algebra ate targetRealisation target genericEstimand procedure}
    (unbiased : Guarantees.FiniteRationalUnbiasedness
      {scope} {algebra} {ate} {targetRealisation}
      target {genericEstimand} procedure)
    (dispersion : FiniteRationalEstimatorDispersion procedure) →
  law dispersion ≡ Guarantees.law unbiased →
  estimateToRational dispersion ≡ Guarantees.estimateToRational unbiased →
  estimatorMean dispersion ≡ FiniteTarget.realisedAggregate target
unbiasednessGivesMeanTargetEquality unbiased dispersion sameLaw sameMap
  rewrite sameLaw | sameMap =
  trans
    (estimatorMeanIsFiniteExpectation dispersion)
    (Guarantees.expectedEstimatorEqualsTarget unbiased)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteVarianceMeansStandardErrorPermission : Set where

data FiniteVarianceMeansAsymptoticVariancePermission : Set where

data LowVarianceMeansUnbiasedPermission : Set where

data LowMSEMeansCausalIdentificationPermission : Set where

data FiniteVarianceMeansNormalSamplingLawPermission : Set where

data VarianceEqualsMSEWithoutMatchingCentrePermission : Set where

finiteVarianceDoesNotBecomeStandardError :
  FiniteVarianceMeansStandardErrorPermission → ⊥
finiteVarianceDoesNotBecomeStandardError ()

finiteVarianceDoesNotBecomeAsymptoticVariance :
  FiniteVarianceMeansAsymptoticVariancePermission → ⊥
finiteVarianceDoesNotBecomeAsymptoticVariance ()

lowVarianceDoesNotBecomeUnbiasedness :
  LowVarianceMeansUnbiasedPermission → ⊥
lowVarianceDoesNotBecomeUnbiasedness ()

lowMSEDoesNotIdentifyCause :
  LowMSEMeansCausalIdentificationPermission → ⊥
lowMSEDoesNotIdentifyCause ()

finiteVarianceDoesNotImplyNormalSamplingLaw :
  FiniteVarianceMeansNormalSamplingLawPermission → ⊥
finiteVarianceDoesNotImplyNormalSamplingLaw ()

varianceMSEEqualityNeedsMatchingCentre :
  VarianceEqualsMSEWithoutMatchingCentrePermission → ⊥
varianceMSEEqualityNeedsMatchingCentre ()

record CausalEstimatorFiniteDispersionBoundary : Set where
  constructor causal-estimator-finite-dispersion-boundary
  field
    finiteSamplingLawReused : Bool
    finiteVarianceExact : Bool
    finiteMSEExact : Bool
    unbiasedMatchingCentreCanIdentifyVarianceWithMSE : Bool
    varianceAutomaticallyMeansStandardError : Bool
    varianceAutomaticallyMeansAsymptoticVariance : Bool
    GaussianSamplingLawInventedHere : Bool

canonicalCausalEstimatorFiniteDispersionBoundary :
  CausalEstimatorFiniteDispersionBoundary
canonicalCausalEstimatorFiniteDispersionBoundary =
  causal-estimator-finite-dispersion-boundary
    true true true true false false false
