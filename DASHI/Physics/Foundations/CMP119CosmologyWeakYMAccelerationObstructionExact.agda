{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyWeakYMAccelerationObstructionExact where

------------------------------------------------------------------------
-- THE SOURCE-DERIVED GRAVITY-SIGN TEST, NOT A CLAIM ABOUT CMP119'S STATE.
--
-- In a locally isotropic FLRW source, A = rho + 3p. With a positive
-- Friedmann matter prefactor K=4 pi G/(3c^2), the acceleration equation is
-- a''/a = Lambda c^2/3 - K A.
--
-- Our *existing actual YM weak-coupling decomposition* proves
-- A_YM = (4 kappa + m) E² + m B² >= 0, in its stated regime.
-- Hence with Lambda=0 and no additional source, a''/a <= 0.
--
-- This is an obstruction to using that SAME physical stress as a
-- cosmological accelerating matter component; it neither rules out an
-- independent positive Lambda nor a renormalized quantum sector outside
-- the assumptions. In particular, no Euclidean metric insertion is
-- identified with Lorentzian rho here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)

import DASHI.Physics.Foundations.CMP119AntigravityWeakCouplingTraceEnergyNoGoExact as YM

friedmannMatterAcceleration :
  ℚ → YM.WeakCouplingYMTraceEnergyData → ℚ
friedmannMatterAcceleration positiveGravitationalFactor weak =
  - (positiveGravitationalFactor * YM.activeStress weak)

friedmannNetAcceleration :
  ℚ → ℚ → YM.WeakCouplingYMTraceEnergyData → ℚ
friedmannNetAcceleration positiveGravitationalFactor lambdaAcceleration weak =
  lambdaAcceleration + friedmannMatterAcceleration positiveGravitationalFactor weak

weakYMOnlyFLRWCannotAccelerateAtZeroLambda :
  ∀ positiveGravitationalFactor weak →
  0ℚ ≤ positiveGravitationalFactor →
  friedmannNetAcceleration positiveGravitationalFactor 0ℚ weak ≤ 0ℚ
weakYMOnlyFLRWCannotAccelerateAtZeroLambda k weak kNonnegative =
  let
    activeNonnegative : 0ℚ ≤ YM.activeStress weak
    activeNonnegative = YM.activeStressNonnegative weak

    positiveProduct :
      0ℚ ≤ k * YM.activeStress weak
    positiveProduct =
      ℚP.*-mono-≤
        kNonnegative activeNonnegative ℚP.≤-refl ℚP.≤-refl

    negativeProductNonpositive :
      - (k * YM.activeStress weak) ≤ 0ℚ
    negativeProductNonpositive =
      subst
        (λ zero → - (k * YM.activeStress weak) ≤ zero)
        (Ring.solve [])
        (ℚP.neg-antimono-≤ positiveProduct)
  in
  subst
    (λ value → value ≤ 0ℚ)
    (sym (Ring.solve-∀ k (YM.activeStress weak)))
    negativeProductNonpositive

positiveFLRWAccelerationForcesCosmologicalTermAboveYMBaseline :
  ∀ k lambdaAcceleration weak →
  0ℚ < friedmannNetAcceleration k lambdaAcceleration weak →
  k * YM.activeStress weak < lambdaAcceleration
positiveFLRWAccelerationForcesCosmologicalTermAboveYMBaseline
    k lambdaAcceleration weak accelerated =
  subst₂ _<_
    (Ring.solve-∀ k (YM.activeStress weak))
    (Ring.solve-∀ k (YM.activeStress weak) lambdaAcceleration)
    (ℚP.+-monoʳ-<
      (k * YM.activeStress weak) accelerated)
