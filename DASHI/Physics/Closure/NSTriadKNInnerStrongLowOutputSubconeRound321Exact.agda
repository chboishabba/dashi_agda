module DASHI.Physics.Closure.NSTriadKNInnerStrongLowOutputSubconeRound321Exact where

------------------------------------------------------------------------
-- ROUND321 / STRONGLY-LOW INNER OUTPUT SUBCONE
--
-- R319/R320 reduce the heterochiral inner-HH relocation route to four exact
-- cross-layer threshold margins.  The two cleanest are
--
--   forcing-high : 3 q <= 2 M,
--   comparable   : 3 p <= 2 M.
--
-- Literal resonance alone does NOT imply these.  This file therefore exposes
-- the genuine additional subcone
--
--   3 p <= 2 M,
--
-- where p is the inner HH->low output and M is the inner high shell.  On the
-- forcing-high orientation, q is the outer low leg, so q <= p.  Monotonicity
-- then gives
--
--   3 q <= 3 p <= 2 M.
--
-- Thus one strongly-low inner-output receipt pays TWO heterochiral-HH outer
-- exponent cells.  This is deliberately stronger than the old R235 deep-HH
-- threshold 5 p <= 4 M and is not identified with it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

one two three : ℚ
one = 1
two = one + one
three = two + one

record StronglyLowInnerOutput : Set where
  constructor strongly-low-inner-output
  field
    pShell innerHighShell : ℚ
    threePBelowTwoM : three * pShell ≤ two * innerHighShell

open StronglyLowInnerOutput public

record ForcingHighOrientation : Set where
  constructor forcing-high-orientation
  field
    qShell pShell : ℚ
    qBelowP : qShell ≤ pShell

open ForcingHighOrientation public

tripleMonotone :
  {a b : ℚ} → a ≤ b → three * a ≤ three * b
tripleMonotone {a} {b} a≤b =
  let
    raw : (a + a) + a ≤ (b + b) + b
    raw = ℚP.+-mono-≤ (ℚP.+-mono-≤ a≤b a≤b) a≤b

    leftMeaning : (a + a) + a ≡ three * a
    leftMeaning = solve (a ∷ [])

    rightMeaning : (b + b) + b ≡ three * b
    rightMeaning = solve (b ∷ [])
  in
  subst
    (λ left → left ≤ three * b)
    leftMeaning
    (subst
      (λ right → (a + a) + a ≤ right)
      rightMeaning
      raw)

forcingHighThresholdFromStronglyLowInnerOutput :
  (S : StronglyLowInnerOutput)
  (O : ForcingHighOrientation) →
  pShell O ≡ pShell S →
  three * qShell O ≤ two * innerHighShell S
forcingHighThresholdFromStronglyLowInnerOutput S O pAgrees =
  let
    q≤p3 : three * qShell O ≤ three * pShell O
    q≤p3 = tripleMonotone (qBelowP O)

    p3≤2M : three * pShell O ≤ two * innerHighShell S
    p3≤2M = subst
      (λ selected → three * selected ≤ two * innerHighShell S)
      (symmetry pAgrees)
      (threePBelowTwoM S)
  in
  ℚP.≤-trans q≤p3 p3≤2M
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

comparableThresholdFromStronglyLowInnerOutput :
  (S : StronglyLowInnerOutput) →
  three * pShell S ≤ two * innerHighShell S
comparableThresholdFromStronglyLowInnerOutput = threePBelowTwoM

round321StronglyLowInnerOutputSubconeIdentified : Bool
round321StronglyLowInnerOutputSubconeIdentified = true

round321ForcingHighHHRelocationExponentCellPaidOnSubcone : Bool
round321ForcingHighHHRelocationExponentCellPaidOnSubcone = true

round321ComparableHHRelocationExponentCellPaidOnSubcone : Bool
round321ComparableHHRelocationExponentCellPaidOnSubcone = true

round321WholeHeterochiralHHRoutePaid : Bool
round321WholeHeterochiralHHRoutePaid = false

round321PhysicalSchurRowColumnClosed : Bool
round321PhysicalSchurRowColumnClosed = false

round321PackageAClosed : Bool
round321PackageAClosed = false

round321ClayPromotion : Bool
round321ClayPromotion = false

round321PackageAClosedIsFalse : round321PackageAClosed ≡ false
round321PackageAClosedIsFalse = refl

round321ClayPromotionIsFalse : round321ClayPromotion ≡ false
round321ClayPromotionIsFalse = refl
