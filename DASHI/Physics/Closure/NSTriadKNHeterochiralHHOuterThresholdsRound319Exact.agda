module DASHI.Physics.Closure.NSTriadKNHeterochiralHHOuterThresholdsRound319Exact where

------------------------------------------------------------------------
-- ROUND319 / NORMAL FORMS FOR THE HETEROCHIRAL-HH RELOCATION THRESHOLD
--
-- R318 says the inner heterochiral HH->low mechanism closes an oriented outer
-- cell whenever
--
--   missingOuterSquaredGain <= 2 (M - p),
--
-- where M is the inner high shell and p is the inner output / outer forcing
-- shell.  This file performs only the exact linear exponent algebra for the
-- four outer regions.  It does not assert that the resulting inequalities hold
-- physically.
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

-- We encode each threshold as equality of the two residual differences.  Thus
-- an upstream ordered-field proof may transport <=0 between the original and
-- normalized forms without any new analytic assumption.

forcingLowThresholdResidual : ℚ → ℚ → ℚ → ℚ
forcingLowThresholdResidual p q innerHigh =
  (three * p - two * q) - two * (innerHigh - p)

forcingLowThresholdNormal : ℚ → ℚ → ℚ → ℚ
forcingLowThresholdNormal p q innerHigh =
  five * p - two * innerHigh - two * q

forcingLowThresholdNormalizes :
  (p q innerHigh : ℚ) →
  forcingLowThresholdResidual p q innerHigh
  ≡ forcingLowThresholdNormal p q innerHigh
forcingLowThresholdNormalizes p q innerHigh =
  solve (p ∷ q ∷ innerHigh ∷ [])

forcingHighThresholdResidual : ℚ → ℚ → ℚ → ℚ
forcingHighThresholdResidual p q innerHigh =
  (three * q - two * p) - two * (innerHigh - p)

forcingHighThresholdNormal : ℚ → ℚ → ℚ → ℚ
forcingHighThresholdNormal p q innerHigh =
  three * q - two * innerHigh

forcingHighThresholdNormalizes :
  (p q innerHigh : ℚ) →
  forcingHighThresholdResidual p q innerHigh
  ≡ forcingHighThresholdNormal p q innerHigh
forcingHighThresholdNormalizes p q innerHigh =
  solve (p ∷ q ∷ innerHigh ∷ [])

hhThresholdResidual : ℚ → ℚ → ℚ → ℚ → ℚ
hhThresholdResidual p k outerHigh innerHigh =
  (five * k - four * outerHigh) - two * (innerHigh - p)

hhThresholdNormal : ℚ → ℚ → ℚ → ℚ → ℚ
hhThresholdNormal p k outerHigh innerHigh =
  five * k + two * p - four * outerHigh - two * innerHigh

hhThresholdNormalizes :
  (p k outerHigh innerHigh : ℚ) →
  hhThresholdResidual p k outerHigh innerHigh
  ≡ hhThresholdNormal p k outerHigh innerHigh
hhThresholdNormalizes p k outerHigh innerHigh =
  solve (p ∷ k ∷ outerHigh ∷ innerHigh ∷ [])

comparableThresholdResidual : ℚ → ℚ → ℚ
comparableThresholdResidual p innerHigh =
  p - two * (innerHigh - p)

comparableThresholdNormal : ℚ → ℚ → ℚ
comparableThresholdNormal p innerHigh =
  three * p - two * innerHigh

comparableThresholdNormalizes :
  (p innerHigh : ℚ) →
  comparableThresholdResidual p innerHigh
  ≡ comparableThresholdNormal p innerHigh
comparableThresholdNormalizes p innerHigh =
  solve (p ∷ innerHigh ∷ [])

round319ForcingLowThresholdNormalized : Bool
round319ForcingLowThresholdNormalized = true

round319ForcingHighThresholdNormalized : Bool
round319ForcingHighThresholdNormalized = true

round319HHThresholdNormalized : Bool
round319HHThresholdNormalized = true

round319ComparableThresholdNormalized : Bool
round319ComparableThresholdNormalized = true

round319AnyThresholdProvedPhysically : Bool
round319AnyThresholdProvedPhysically = false

round319PackageAClosed : Bool
round319PackageAClosed = false

round319ClayPromotion : Bool
round319ClayPromotion = false

round319PackageAClosedIsFalse : round319PackageAClosed ≡ false
round319PackageAClosedIsFalse = refl
