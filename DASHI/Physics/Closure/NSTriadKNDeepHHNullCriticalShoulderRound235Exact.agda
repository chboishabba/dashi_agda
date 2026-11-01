module DASHI.Physics.Closure.NSTriadKNDeepHHNullCriticalShoulderRound235Exact where

------------------------------------------------------------------------
-- ROUND235 / HH NULL GAIN: EXACT DYADIC PAYMENT THRESHOLD
--
-- Round232 identifies the opposite-helicity HH->low null factor
--
--   |B_+-(k,p,q)|^2  ~  2^(2(j-m))
--
-- when |p| ~ |q| ~ 2^m and |k| ~ 2^j.
--
-- For a fixed low-output shell, Cauchy-Schwarz on each convolution fibre and
-- square summation over the O(2^(3j)) output modes gives the squared spatial
-- coefficient
--
--   2^(3j) * 2^(2(j-m)) = 2^(5j-2m).
--
-- Paying one high factor with the Leray H1 dissipation contributes another
-- 2^(2m), so energy+dissipation closes exactly in the deep-HH region
--
--   5 j <= 4 m.                                             (DHH)
--
-- Therefore the usual fixed-gap HH->low class still contains a critical
-- shoulder whenever
--
--   4 m < 5 j.
--
-- This is the HH analogue of Round234's deep-FL / critical-shoulder split.
-- The post-Round235 critical core is not merely constant-width comparable:
-- it includes both the FL shoulder and the HH output shoulder.
--
-- This module formalises only the exact exponent arithmetic.  The physical
-- helical-basis/angular weld and the concrete finite-shell convolution bound
-- remain separate analytic producers; no diagnostic calculation is promoted
-- to a proof receipt here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

one two three four five : ℚ
one = 1ℚ
two = one + one
three = two + one
four = two + two
five = four + one

hhOutputCountingExponent : ℚ → ℚ
hhOutputCountingExponent outputShell = three * outputShell

hhNullSquaredGainExponent : ℚ → ℚ → ℚ
hhNullSquaredGainExponent outputShell highShell =
  two * (outputShell - highShell)

hhSquaredSpatialExponent : ℚ → ℚ → ℚ
hhSquaredSpatialExponent outputShell highShell =
  hhOutputCountingExponent outputShell
  + hhNullSquaredGainExponent outputShell highShell

hhSquaredSpatialExponentIsFiveJMinusTwoM :
  (j m : ℚ) →
  hhSquaredSpatialExponent j m ≡ five * j - two * m
hhSquaredSpatialExponentIsFiveJMinusTwoM j m = solve (j ∷ m ∷ [])

lerayHighSquaredExponent : ℚ → ℚ
lerayHighSquaredExponent highShell = two * highShell

-- The exponent gap after paying one high factor with H1 dissipation.
hhResidualSquaredExponent : ℚ → ℚ → ℚ
hhResidualSquaredExponent outputShell highShell =
  hhSquaredSpatialExponent outputShell highShell
  - lerayHighSquaredExponent highShell

hhResidualSquaredExponentIsFiveJMinusFourM :
  (j m : ℚ) →
  hhResidualSquaredExponent j m ≡ five * j - four * m
hhResidualSquaredExponentIsFiveJMinusFourM j m = solve (j ∷ m ∷ [])

-- Integer-ratio version of the threshold: j = 4r and m = 5r lies exactly on
-- the boundary 5j = 4m, avoiding any division or square-root authority.
hhCriticalThresholdAtFourFifths : (r : ℚ) →
  five * (four * r) ≡ four * (five * r)
hhCriticalThresholdAtFourFifths r = solve (r ∷ [])

round235HHNullSquaredGainUsed : Bool
round235HHNullSquaredGainUsed = true

round235DeepHHThresholdIdentified : Bool
round235DeepHHThresholdIdentified = true

round235EntireFixedGapHHRegionEnergyPayable : Bool
round235EntireFixedGapHHRegionEnergyPayable = false

round235CriticalHHOutputShoulderRemains : Bool
round235CriticalHHOutputShoulderRemains = true

round235PhysicalHHConvolutionPaymentClosed : Bool
round235PhysicalHHConvolutionPaymentClosed = false

round235CriticalCoreIsOnlyComparable : Bool
round235CriticalCoreIsOnlyComparable = false

round235PackageAClosed : Bool
round235PackageAClosed = false

round235ClayPromotion : Bool
round235ClayPromotion = false

round235HHNullSquaredGainUsedIsTrue :
  round235HHNullSquaredGainUsed ≡ true
round235HHNullSquaredGainUsedIsTrue = refl

round235DeepHHThresholdIdentifiedIsTrue :
  round235DeepHHThresholdIdentified ≡ true
round235DeepHHThresholdIdentifiedIsTrue = refl

round235EntireFixedGapHHRegionEnergyPayableIsFalse :
  round235EntireFixedGapHHRegionEnergyPayable ≡ false
round235EntireFixedGapHHRegionEnergyPayableIsFalse = refl

round235CriticalHHOutputShoulderRemainsIsTrue :
  round235CriticalHHOutputShoulderRemains ≡ true
round235CriticalHHOutputShoulderRemainsIsTrue = refl

round235PackageAClosedIsFalse : round235PackageAClosed ≡ false
round235PackageAClosedIsFalse = refl

round235ClayPromotionIsFalse : round235ClayPromotion ≡ false
round235ClayPromotionIsFalse = refl
