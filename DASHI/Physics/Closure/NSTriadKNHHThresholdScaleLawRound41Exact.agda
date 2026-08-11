module DASHI.Physics.Closure.NSTriadKNHHThresholdScaleLawRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 40 proved that the exact HH tax
--
--   f_q(r) = A_q r + B_q r^-2
--
-- is globally minimized at every positive rational r_q satisfying
--
--   A_q r_q^3 = 2 B_q.
--
-- The continuation analysis proposed reading the *scale law of A_q/B_q*
-- before assuming a global coherence threshold.  This file makes two useful
-- cases exact.
--
-- 1. If A_q and B_q carry the same nonnegative shell factor, one balanced
--    base scale is balanced at every shell.  The scale-independent threshold
--    is therefore a theorem, not an assumption.
--
-- 2. If A is unchanged while B drops by 1/8 from one shell to the next, the
--    balanced r drops by 1/2 and delta=r^2 drops by 1/4.  This is the exact
--    dyadic realization of the cubic exponent law r ~ (B/A)^(1/3), with no
--    cube-root primitive.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHAnalyticThresholdOptimizerRound40Exact as Opt
import DASHI.Physics.Closure.NSTriadKNHHScaleDependentThresholdRound40Exact as Scale

half quarter eighth : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4
eighth = Int.+ 1 / 8

multiplyNonnegative : ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
multiplyNonnegative {left} {right} leftNN rightNN =
  let
    instance
      leftNNI = nonNegative leftNN
      rightNNI = nonNegative rightNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

record CommonFactorHHCoefficients : Set₁ where
  field
    baseA baseB : ℚ
    shellFactor : Nat → ℚ
    shellFactorNonnegative : (shell : Nat) → 0ℚ ≤ shellFactor shell
    baseBalance : Opt.BalancedHHThreshold baseA baseB

open CommonFactorHHCoefficients public

commonFactorA commonFactorB : CommonFactorHHCoefficients → Nat → ℚ
commonFactorA coefficients shell =
  shellFactor coefficients shell * baseA coefficients
commonFactorB coefficients shell =
  shellFactor coefficients shell * baseB coefficients

commonFactorBalancedAt :
  (coefficients : CommonFactorHHCoefficients) →
  (shell : Nat) →
  Opt.BalancedHHThreshold
    (commonFactorA coefficients shell)
    (commonFactorB coefficients shell)
commonFactorBalancedAt coefficients shell = record
  { selectedScale = Opt.selectedScale (baseBalance coefficients)
  ; A-nonnegative = multiplyNonnegative
      (shellFactorNonnegative coefficients shell)
      (Opt.A-nonnegative (baseBalance coefficients))
  ; B-nonnegative = multiplyNonnegative
      (shellFactorNonnegative coefficients shell)
      (Opt.B-nonnegative (baseBalance coefficients))
  ; cubicBalance = balance
  }
  where
  weight = shellFactor coefficients shell
  A0 = baseA coefficients
  B0 = baseB coefficients
  r = Opt.scaleValue (Opt.selectedScale (baseBalance coefficients))

  scaled :
    weight * (A0 * r * r * r)
    ≡ weight * (Opt.two * B0)
  scaled = cong (weight *_) (Opt.cubicBalance (baseBalance coefficients))

  leftMeaning :
    (weight * A0) * r * r * r
    ≡ weight * (A0 * r * r * r)
  leftMeaning = solve (weight ∷ A0 ∷ r ∷ [])

  rightMeaning :
    weight * (Opt.two * B0)
    ≡ Opt.two * (weight * B0)
  rightMeaning = solve (weight ∷ B0 ∷ [])

  balance :
    commonFactorA coefficients shell * r * r * r
    ≡ Opt.two * commonFactorB coefficients shell
  balance = trans leftMeaning (trans scaled rightMeaning)

commonFactorThresholdProfile :
  CommonFactorHHCoefficients → Scale.ShellHHThresholdProfile
commonFactorThresholdProfile coefficients = record
  { A = commonFactorA coefficients
  ; B = commonFactorB coefficients
  ; balanced = commonFactorBalancedAt coefficients
  }

commonFactorSelectedScaleIsBase :
  (coefficients : CommonFactorHHCoefficients) →
  (shell : Nat) →
  Scale.selectedScaleAt (commonFactorThresholdProfile coefficients) shell
  ≡ Opt.selectedScale (baseBalance coefficients)
commonFactorSelectedScaleIsBase coefficients shell = refl

commonFactorRecoversScaleIndependentThreshold :
  (coefficients : CommonFactorHHCoefficients) →
  Scale.ScaleIndependentBalancedThreshold
    (commonFactorThresholdProfile coefficients)
commonFactorRecoversScaleIndependentThreshold coefficients = record
  { commonScale = Opt.selectedScale (baseBalance coefficients)
  ; selectedScaleIsCommon = commonFactorSelectedScaleIsBase coefficients
  }

------------------------------------------------------------------------
-- Exact cubic dyadic law.
------------------------------------------------------------------------

eighthBadCoefficientForcesHalfBalancedScale :
  ∀ A B r →
  A * r * r * r ≡ Opt.two * B →
  A * (half * r) * (half * r) * (half * r)
  ≡ Opt.two * (eighth * B)
eighthBadCoefficientForcesHalfBalancedScale A B r balance =
  let
    scaled :
      eighth * (A * r * r * r)
      ≡ eighth * (Opt.two * B)
    scaled = cong (eighth *_) balance
  in
  trans
    (solve (A ∷ r ∷ []))
    (trans scaled (solve (B ∷ [])))

halfBalancedScaleQuartersDelta :
  ∀ r →
  L2.square (half * r) ≡ quarter * L2.square r
halfBalancedScaleQuartersDelta r = solve (r ∷ [])

commonFactorThresholdLawClosed : Bool
commonFactorThresholdLawClosed = true

dyadicCubicThresholdLawClosed : Bool
dyadicCubicThresholdLawClosed = true

physicalHHCoefficientScaleLawConstructed : Bool
physicalHHCoefficientScaleLawConstructed = false

commonFactorThresholdLawClosedIsTrue :
  commonFactorThresholdLawClosed ≡ true
commonFactorThresholdLawClosedIsTrue = refl

dyadicCubicThresholdLawClosedIsTrue :
  dyadicCubicThresholdLawClosed ≡ true
dyadicCubicThresholdLawClosedIsTrue = refl
