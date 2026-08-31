module DASHI.Physics.Closure.NSTriadKNStrongLowPaysOuterHHRound323Exact where

------------------------------------------------------------------------
-- ROUND323 / STRONGLY-LOW INNER OUTPUT ALSO PAYS THE OUTER-HH CELL
--
-- R322 leaves only the outer-HH orientation of the heterochiral inner-HH
-- relocation route.  Its R319 threshold is
--
--   5 k + 2 p <= 4 m_out + 2 M.
--
-- On an outer HH->low shell classification the output shell k is no higher
-- than either declared high input scale:
--
--   k <= m_out,
--   k <= p.
--
-- Therefore
--
--   5k <= 4 m_out + p.
--
-- R321's strongly-low inner receipt gives
--
--   3p <= 2M.
--
-- Adding 2p to the first inequality and then using 3p <= 2M yields the exact
-- R319 outer-HH threshold.  Thus the same strongly-low inner-output subcone
-- exponent-pays ALL FOUR outer orientations of the heterochiral-HH route.
--
-- This remains exponent-level plumbing.  The physical R120/R232 same-object
-- weld and the cutoff-uniform Schur row/column estimate are still separate.
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
import DASHI.Physics.Closure.NSTriadKNStrongLowPaysOrientedFLRound322Exact as R322

one two three four five : ℚ
one = 1
two = one + one
three = two + one
four = two + two
five = four + one

record OuterHHOrdering : Set where
  constructor outer-hh-ordering
  field
    kShell pShell outerHighShell : ℚ
    kBelowP : kShell ≤ pShell
    kBelowOuterHigh : kShell ≤ outerHighShell

open OuterHHOrdering public

quadrupleMonotone :
  {a b : ℚ} → a ≤ b → four * a ≤ four * b
quadrupleMonotone {a} {b} a≤b =
  let
    twice : a + a ≤ b + b
    twice = ℚP.+-mono-≤ a≤b a≤b

    raw : (a + a) + (a + a) ≤ (b + b) + (b + b)
    raw = ℚP.+-mono-≤ twice twice

    leftMeaning : (a + a) + (a + a) ≡ four * a
    leftMeaning = solve (a ∷ [])

    rightMeaning : (b + b) + (b + b) ≡ four * b
    rightMeaning = solve (b ∷ [])
  in
  subst
    (λ left → left ≤ four * b)
    leftMeaning
    (subst
      (λ right → (a + a) + (a + a) ≤ right)
      rightMeaning
      raw)

outerHHFiveKBelowFourMPlusP :
  (O : OuterHHOrdering) →
  five * kShell O ≤ four * outerHighShell O + pShell O
outerHHFiveKBelowFourMPlusP O =
  let
    fourPart : four * kShell O ≤ four * outerHighShell O
    fourPart = quadrupleMonotone (kBelowOuterHigh O)

    added :
      four * kShell O + kShell O
      ≤ four * outerHighShell O + pShell O
    added = ℚP.+-mono-≤ fourPart (kBelowP O)

    leftMeaning : four * kShell O + kShell O ≡ five * kShell O
    leftMeaning = solve (kShell O ∷ [])
  in
  subst
    (λ left → left ≤ four * outerHighShell O + pShell O)
    leftMeaning
    added

outerHHThresholdFromStronglyLowInnerOutput :
  (S : R321.StronglyLowInnerOutput)
  (O : OuterHHOrdering) →
  pShell O ≡ R321.pShell S →
  five * kShell O + two * pShell O
  ≤ four * outerHighShell O + two * R321.innerHighShell S
outerHHThresholdFromStronglyLowInnerOutput S O pAgrees =
  let
    first : five * kShell O ≤ four * outerHighShell O + pShell O
    first = outerHHFiveKBelowFourMPlusP O

    addTwoP :
      five * kShell O + two * pShell O
      ≤ (four * outerHighShell O + pShell O) + two * pShell O
    addTwoP = ℚP.+-mono-≤ first ℚP.≤-refl

    regroupRight :
      (four * outerHighShell O + pShell O) + two * pShell O
      ≡ four * outerHighShell O + three * pShell O
    regroupRight = solve (outerHighShell O ∷ pShell O ∷ [])

    stepTwo :
      five * kShell O + two * pShell O
      ≤ four * outerHighShell O + three * pShell O
    stepTwo = subst
      (λ right → five * kShell O + two * pShell O ≤ right)
      regroupRight
      addTwoP

    strongAtO : three * pShell O ≤ two * R321.innerHighShell S
    strongAtO = subst
      (λ selected → three * selected ≤ two * R321.innerHighShell S)
      (symmetry pAgrees)
      (R321.threePBelowTwoM S)

    finalStep :
      four * outerHighShell O + three * pShell O
      ≤ four * outerHighShell O + two * R321.innerHighShell S
    finalStep = ℚP.+-mono-≤ ℚP.≤-refl strongAtO
  in
  ℚP.≤-trans stepTwo finalStep
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

round323OuterHHOrderingExposesFiveKBound : Bool
round323OuterHHOrderingExposesFiveKBound = true

round323StronglyLowPaysOuterHHThreshold : Bool
round323StronglyLowPaysOuterHHThreshold = true

round323StronglyLowPaysAllFourHeterochiralHHOuterExponentCells : Bool
round323StronglyLowPaysAllFourHeterochiralHHOuterExponentCells = true

round323PhysicalR120R232SameObjectWeldClosed : Bool
round323PhysicalR120R232SameObjectWeldClosed = false

round323PhysicalSchurRowColumnClosed : Bool
round323PhysicalSchurRowColumnClosed = false

round323PackageAClosed : Bool
round323PackageAClosed = false

round323ClayPromotion : Bool
round323ClayPromotion = false

round323PackageAClosedIsFalse : round323PackageAClosed ≡ false
round323PackageAClosedIsFalse = refl

round323ClayPromotionIsFalse : round323ClayPromotion ≡ false
round323ClayPromotionIsFalse = refl
