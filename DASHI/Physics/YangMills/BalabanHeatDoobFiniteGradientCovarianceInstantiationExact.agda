{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobFiniteGradientCovarianceInstantiationExact where

------------------------------------------------------------------------
-- FINITE CONDITIONAL LAW -> ROUND102 TEMPORAL GRADIENT COVARIANCE
--
-- Round102 historically asked for a field
--
--   covarianceDebt n <= 2 * localizedGradientShell n * companionBound.
--
-- On a concrete finite conditional probability this is not an independent
-- analytic theorem.  Define covarianceDebt to be the absolute covariance of
-- the actual first-gradient observables and derive the bound from the internal
-- finite bounded-covariance theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteBoundedCovarianceExact as FiniteCov
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Grad

record FiniteTemporalGradientCovarianceData (State : Set) : Set₁ where
  field
    probabilityAt : Nat → FiniteCov.FiniteRationalProbability State

    localizedGradient companionGradient :
      Nat → FiniteCov.Observable State

    localizedGradientShell : Nat → ℚ
    localizedGradientNonnegative :
      ∀ n → 0ℚ ≤ localizedGradientShell n

    gradientAmplitude : ℚ
    gradientAmplitudeNonnegative : 0ℚ ≤ gradientAmplitude
    localizedGradientGeometricHalf : ∀ n →
      localizedGradientShell n
      ≤ gradientAmplitude
          * DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact.halfPower n

    companionGradientBound : ℚ
    companionGradientBoundNonnegative : 0ℚ ≤ companionGradientBound

    localizedGradientPointwiseBound : ∀ n →
      FiniteCov.PointwiseBounded
        (localizedGradient n)
        (localizedGradientShell n)

    companionGradientPointwiseBound : ∀ n →
      FiniteCov.PointwiseBounded
        (companionGradient n)
        companionGradientBound

open FiniteTemporalGradientCovarianceData public

finiteCovarianceDebt :
  ∀ {State} → FiniteTemporalGradientCovarianceData State → Nat → ℚ
finiteCovarianceDebt dataSet n =
  ∣ FiniteCov.covariance
      (probabilityAt dataSet n)
      (localizedGradient dataSet n)
      (companionGradient dataSet n) ∣

finiteCovarianceDebtNonnegative :
  ∀ {State} (dataSet : FiniteTemporalGradientCovarianceData State) n →
  0ℚ ≤ finiteCovarianceDebt dataSet n
finiteCovarianceDebtNonnegative dataSet n =
  ℚP.0≤∣p∣
    (FiniteCov.covariance
      (probabilityAt dataSet n)
      (localizedGradient dataSet n)
      (companionGradient dataSet n))

finiteCovarianceBelowTwoGradientProducts :
  ∀ {State} (dataSet : FiniteTemporalGradientCovarianceData State) n →
  finiteCovarianceDebt dataSet n
  ≤ Grad.two
      * (localizedGradientShell dataSet n
          * companionGradientBound dataSet)
finiteCovarianceBelowTwoGradientProducts dataSet n =
  subst
    (λ upper → finiteCovarianceDebt dataSet n ≤ upper)
    (ℚRing.solve-∀
      Grad.two
      (localizedGradientShell dataSet n)
      (companionGradientBound dataSet))
    (FiniteCov.boundedCovariance
      (probabilityAt dataSet n)
      (localizedGradient dataSet n)
      (companionGradient dataSet n)
      (localizedGradientShell dataSet n)
      (companionGradientBound dataSet)
      (localizedGradientNonnegative dataSet n)
      (companionGradientBoundNonnegative dataSet)
      (localizedGradientPointwiseBound dataSet n)
      (companionGradientPointwiseBound dataSet n))

asHeatDoobTemporalGradientCovariance :
  ∀ {State} →
  FiniteTemporalGradientCovarianceData State →
  Grad.HeatDoobTemporalGradientCovariance
asHeatDoobTemporalGradientCovariance dataSet = record
  { Grad.HeatDoobTemporalGradientCovariance.localizedGradientShell =
      localizedGradientShell dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.localizedGradientNonnegative =
      localizedGradientNonnegative dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.gradientAmplitude =
      gradientAmplitude dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.gradientAmplitudeNonnegative =
      gradientAmplitudeNonnegative dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.localizedGradientGeometricHalf =
      localizedGradientGeometricHalf dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.companionGradientBound =
      companionGradientBound dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.companionGradientBoundNonnegative =
      companionGradientBoundNonnegative dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.covarianceDebt =
      finiteCovarianceDebt dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.covarianceDebtNonnegative =
      finiteCovarianceDebtNonnegative dataSet
  ; Grad.HeatDoobTemporalGradientCovariance.covarianceBelowTwoGradientProducts =
      finiteCovarianceBelowTwoGradientProducts dataSet
  }

finiteHeatDoobGradientCovarianceInstantiationLevel : ProofLevel
finiteHeatDoobGradientCovarianceInstantiationLevel = machineChecked
