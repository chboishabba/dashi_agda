module DASHI.Physics.Closure.NSTriadKNParabolicCriticalFrequencyConeRound236Exact where

------------------------------------------------------------------------
-- ROUND236 / PAID REGIONS VS PARABOLIC CRITICAL FREQUENCY CONE
--
-- Rounds234--235 sharpen the old fixed-gap Bony taxonomy by asking the exact
-- backward question forced by the Leray budgets: which dyadic interactions
-- can be paid by one L_t^infinity L_x^2 energy factor and one
-- L_t^2 H_x^1 dissipation factor after using the available symbol geometry?
--
-- Deep low-high/high-low:
--
--   3 j_low <= 2 j_high.
--
-- Deep HH->low after the opposite-helicity null gain:
--
--   5 j_out <= 4 j_high.
--
-- Everything outside those inequalities remains critical.  Thus the object
-- that a concentration/compactness argument must own is not merely the old
-- constant-width comparable class.  It is the PARABOLIC CRITICAL CONE:
--
--   LH/HL shoulder : 2 j_high < 3 j_low,
--   HH shoulder    : 4 j_high < 5 j_out,
--   plus the ordinary comparable class.
--
-- A sequence may lie in the shoulder while its shell gap still tends to
-- infinity (e.g. j_low ~ .7 j_high).  Such a sequence is scale-orthogonal in
-- the profile-decomposition sense even though it is not energy-payable by the
-- elementary dyadic estimate.  This is precisely why the next mathematical
-- step is profile extraction / rigidity rather than a wider fixed-gap Bony
-- estimate.
--
-- This file is a decision surface only.  It does not assert profile
-- decomposition, orthogonality-decoupling, or the final rigidity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234
import DASHI.Physics.Closure.NSTriadKNDeepHHNullCriticalShoulderRound235Exact as R235

one two three four five : ℚ
one = 1ℚ
two = one + one
three = two + one
four = two + two
five = four + one

farLowResidualExponent : ℚ → ℚ → ℚ
farLowResidualExponent lowShell highShell =
  three * lowShell - two * highShell

hhResidualExponent : ℚ → ℚ → ℚ
hhResidualExponent outputShell highShell =
  five * outputShell - four * highShell

farLowResidualMatchesRound234 :
  (low high : ℚ) →
  farLowResidualExponent low high
  ≡ R234.criticalShoulderExcess low high
farLowResidualMatchesRound234 low high = solve (low ∷ high ∷ [])

hhResidualMatchesRound235 :
  (output high : ℚ) →
  hhResidualExponent output high
  ≡ R235.hhResidualSquaredExponent output high
hhResidualMatchesRound235 output high = solve (output ∷ high ∷ [])

-- Boundary rays written without fractions.
farLowBoundaryRay : (r : ℚ) →
  three * (two * r) ≡ two * (three * r)
farLowBoundaryRay r = solve (r ∷ [])

hhBoundaryRay : (r : ℚ) →
  five * (four * r) ≡ four * (five * r)
hhBoundaryRay r = solve (r ∷ [])

round236DeepFarLowEnergyPayableRegionIdentified : Bool
round236DeepFarLowEnergyPayableRegionIdentified =
  R234.round234DeepFarLowExponentThresholdIdentified

round236DeepHHNullEnergyPayableRegionIdentified : Bool
round236DeepHHNullEnergyPayableRegionIdentified =
  R235.round235DeepHHThresholdIdentified

round236CriticalConeStrictlyLargerThanComparableClass : Bool
round236CriticalConeStrictlyLargerThanComparableClass = true

round236ScaleOrthogonalityNeededForShoulders : Bool
round236ScaleOrthogonalityNeededForShoulders = true

round236ProfileDecompositionInstalled : Bool
round236ProfileDecompositionInstalled = false

round236CrossProfileCriticalConeDecouplingClosed : Bool
round236CrossProfileCriticalConeDecouplingClosed = false

round236CompactCriticalTrajectoryExtracted : Bool
round236CompactCriticalTrajectoryExtracted = false

round236RigidityClosed : Bool
round236RigidityClosed = false

round236PackageAClosed : Bool
round236PackageAClosed = false

round236ClayPromotion : Bool
round236ClayPromotion = false

round236DeepFarLowEnergyPayableRegionIdentifiedIsTrue :
  round236DeepFarLowEnergyPayableRegionIdentified ≡ true
round236DeepFarLowEnergyPayableRegionIdentifiedIsTrue = refl

round236DeepHHNullEnergyPayableRegionIdentifiedIsTrue :
  round236DeepHHNullEnergyPayableRegionIdentified ≡ true
round236DeepHHNullEnergyPayableRegionIdentifiedIsTrue = refl

round236CriticalConeStrictlyLargerThanComparableClassIsTrue :
  round236CriticalConeStrictlyLargerThanComparableClass ≡ true
round236CriticalConeStrictlyLargerThanComparableClassIsTrue = refl

round236ScaleOrthogonalityNeededForShouldersIsTrue :
  round236ScaleOrthogonalityNeededForShoulders ≡ true
round236ScaleOrthogonalityNeededForShouldersIsTrue = refl

round236ProfileDecompositionInstalledIsFalse :
  round236ProfileDecompositionInstalled ≡ false
round236ProfileDecompositionInstalledIsFalse = refl

round236RigidityClosedIsFalse : round236RigidityClosed ≡ false
round236RigidityClosedIsFalse = refl

round236PackageAClosedIsFalse : round236PackageAClosed ≡ false
round236PackageAClosedIsFalse = refl

round236ClayPromotionIsFalse : round236ClayPromotion ≡ false
round236ClayPromotionIsFalse = refl
