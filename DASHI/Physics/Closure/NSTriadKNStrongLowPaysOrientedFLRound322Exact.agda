module DASHI.Physics.Closure.NSTriadKNStrongLowPaysOrientedFLRound322Exact where

------------------------------------------------------------------------
-- ROUND322 / STRONGLY-LOW INNER HH OUTPUT PAYS BOTH ORIENTED FL CELLS
--
-- R321 proves that
--
--   3 p <= 2 M
--
-- pays the heterochiral-HH relocation threshold for the forcing-high and
-- comparable outer cells.  The forcing-low threshold from R319 is
--
--   5 p <= 2 M + 2 q.
--
-- On the forcing-low orientation p <= q.  Hence
--
--   3p <= 2M,
--   2p <= 2q
--
-- add to the desired threshold.  Thus the SAME strongly-low inner-output
-- receipt pays forcing-low, forcing-high, and comparable.  Only the outer-HH
-- orientation remains genuinely different inside this heterochiral-HH route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNInnerStrongLowOutputSubconeRound321Exact as R321

one two three five : ℚ
one = 1
two = one + one
three = two + one
five = three + two

doubleMonotone :
  {a b : ℚ} → a ≤ b → two * a ≤ two * b
doubleMonotone {a} {b} a≤b =
  let
    raw : a + a ≤ b + b
    raw = ℚP.+-mono-≤ a≤b a≤b

    leftMeaning : a + a ≡ two * a
    leftMeaning = solve (a ∷ [])

    rightMeaning : b + b ≡ two * b
    rightMeaning = solve (b ∷ [])
  in
  subst
    (λ left → left ≤ two * b)
    leftMeaning
    (subst
      (λ right → a + a ≤ right)
      rightMeaning
      raw)

forcingLowThresholdFromStronglyLowInnerOutput :
  (S : R321.StronglyLowInnerOutput)
  (q : ℚ) →
  R321.pShell S ≤ q →
  five * R321.pShell S
  ≤ two * R321.innerHighShell S + two * q
forcingLowThresholdFromStronglyLowInnerOutput S q p≤q =
  let
    threePart :
      three * R321.pShell S ≤ two * R321.innerHighShell S
    threePart = R321.threePBelowTwoM S

    twoPart : two * R321.pShell S ≤ two * q
    twoPart = doubleMonotone p≤q

    added :
      three * R321.pShell S + two * R321.pShell S
      ≤ two * R321.innerHighShell S + two * q
    added = ℚP.+-mono-≤ threePart twoPart

    leftMeaning :
      three * R321.pShell S + two * R321.pShell S
      ≡ five * R321.pShell S
    leftMeaning = solve (R321.pShell S ∷ [])
  in
  subst
    (λ left → left ≤ two * R321.innerHighShell S + two * q)
    leftMeaning
    added

round322StronglyLowPaysForcingLowThreshold : Bool
round322StronglyLowPaysForcingLowThreshold = true

round322StronglyLowPaysForcingHighThreshold : Bool
round322StronglyLowPaysForcingHighThreshold =
  R321.round321ForcingHighHHRelocationExponentCellPaidOnSubcone

round322StronglyLowPaysComparableThreshold : Bool
round322StronglyLowPaysComparableThreshold =
  R321.round321ComparableHHRelocationExponentCellPaidOnSubcone

round322StronglyLowPaysThreeOfFourHeterochiralHHOuterCells : Bool
round322StronglyLowPaysThreeOfFourHeterochiralHHOuterCells = true

round322OuterHHCellPaidByStrongLowAlone : Bool
round322OuterHHCellPaidByStrongLowAlone = false

round322PhysicalSchurRowColumnClosed : Bool
round322PhysicalSchurRowColumnClosed = false

round322PackageAClosed : Bool
round322PackageAClosed = false

round322ClayPromotion : Bool
round322ClayPromotion = false

round322PackageAClosedIsFalse : round322PackageAClosed ≡ false
round322PackageAClosedIsFalse = refl

round322ClayPromotionIsFalse : round322ClayPromotion ≡ false
round322ClayPromotionIsFalse = refl
