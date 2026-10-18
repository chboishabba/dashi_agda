{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityTimelikeEnergySharpActiveStressCriterionExact where

------------------------------------------------------------------------
-- LORENTZIAN SAME-TENSOR SHARP SIGN CRITERION
--
-- A = Theta + 2 rho, hence A<0 iff 2 rho < -Theta.
-- A negative trace alone is not enough. With zero spatial pressures and
-- positive rho, Theta = -rho < 0 but A = rho > 0.
--
-- This is rational arithmetic on the SAME stress tensor; the actual
-- selected CMP119 measure and timelike insertions are a distinct source leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (sym; subst; subst₂)
import DASHI.Physics.Foundations.CMP119AntigravityTraceVsActiveStressFirewallExact as Stress

two : ℚ
two = 1ℚ + 1ℚ

activeNegativeImpliesEnergyControl :
  ∀ theta rho →
  theta + two * rho < 0ℚ →
  two * rho < - theta
activeNegativeImpliesEnergyControl theta rho activeNegative =
  subst₂ _<_
    (Ring.solve-∀ theta rho)
    (Ring.solve-∀ theta)
    (ℚP.+-monoʳ-< (- theta) activeNegative)

energyControlImpliesActiveNegative :
  ∀ theta rho →
  two * rho < - theta →
  theta + two * rho < 0ℚ
energyControlImpliesActiveNegative theta rho energyControl =
  subst₂ _<_
    (Ring.solve-∀ theta rho)
    (Ring.solve-∀ theta)
    (ℚP.+-monoʳ-< theta energyControl)

selectedActiveNegativeImpliesTimelikeEnergyControl :
  ∀ rho px py pz →
  Stress.lorentzianActiveStress rho px py pz < 0ℚ →
  two * rho < - Stress.lorentzianTrace rho px py pz
selectedActiveNegativeImpliesTimelikeEnergyControl rho px py pz negative =
  activeNegativeImpliesEnergyControl
    (Stress.lorentzianTrace rho px py pz) rho
    (subst
      (λ value → value < 0ℚ)
      (Stress.activeStressIsTracePlusTwiceEnergyDensity rho px py pz)
      negative)

selectedTimelikeEnergyControlImpliesActiveNegative :
  ∀ rho px py pz →
  two * rho < - Stress.lorentzianTrace rho px py pz →
  Stress.lorentzianActiveStress rho px py pz < 0ℚ
selectedTimelikeEnergyControlImpliesActiveNegative rho px py pz control =
  subst
    (λ value → value < 0ℚ)
    (sym (Stress.activeStressIsTracePlusTwiceEnergyDensity rho px py pz))
    (energyControlImpliesActiveNegative
      (Stress.lorentzianTrace rho px py pz) rho control)

zeroPressureTraceEqualsNegativeEnergy :
  ∀ rho →
  Stress.lorentzianTrace rho 0ℚ 0ℚ 0ℚ ≡ - rho
zeroPressureTraceEqualsNegativeEnergy rho = Ring.solve-∀ rho

zeroPressureActiveEqualsEnergy :
  ∀ rho →
  Stress.lorentzianActiveStress rho 0ℚ 0ℚ 0ℚ ≡ rho
zeroPressureActiveEqualsEnergy rho = Ring.solve-∀ rho

zeroPressureTraceStrictlyNegative :
  ∀ rho → 0ℚ < rho →
  Stress.lorentzianTrace rho 0ℚ 0ℚ 0ℚ < 0ℚ
zeroPressureTraceStrictlyNegative rho positive =
  subst
    (λ value → value < 0ℚ)
    (sym (zeroPressureTraceEqualsNegativeEnergy rho))
    (ℚP.neg-antimono-< positive)

zeroPressureActiveStrictlyPositive :
  ∀ rho → 0ℚ < rho →
  0ℚ < Stress.lorentzianActiveStress rho 0ℚ 0ℚ 0ℚ
zeroPressureActiveStrictlyPositive rho positive =
  subst
    (λ value → 0ℚ < value)
    (sym (zeroPressureActiveEqualsEnergy rho))
    positive
