module DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact where

------------------------------------------------------------------------
-- ROUND539 / GENERIC SYMMETRIC UNORDERED <-> ORDERED OFF-DIAGONAL IDENTITY
--
-- For any rational-valued symmetric pair function F on a finite list,
--
--   U(xs) = sum over list-position pairs i<j F(x_i,x_j)
--
-- and
--
--   O(xs) = sum over ordered pairs i!=j F(x_i,x_j),
--
-- satisfy exactly
--
--   O(xs) = 2 * U(xs).
--
-- This is the finite combinatorial compiler needed after R538.  It introduces
-- no Navier--Stokes hypothesis, sign estimate, norm, or cutoff factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂)

rowSum :
  ∀ {A : Set} → (A → A → ℚ) → A → List A → ℚ
rowSum F x [] = 0ℚ
rowSum F x (y ∷ rest) = F x y + rowSum F x rest

columnSum :
  ∀ {A : Set} → (A → A → ℚ) → List A → A → ℚ
columnSum F [] x = 0ℚ
columnSum F (y ∷ rest) x = F y x + columnSum F rest x

unorderedPairSum :
  ∀ {A : Set} → (A → A → ℚ) → List A → ℚ
unorderedPairSum F [] = 0ℚ
unorderedPairSum F (x ∷ rest) =
  rowSum F x rest + unorderedPairSum F rest

orderedOffDiagonalSum :
  ∀ {A : Set} → (A → A → ℚ) → List A → ℚ
orderedOffDiagonalSum F [] = 0ℚ
orderedOffDiagonalSum F (x ∷ rest) =
  rowSum F x rest + columnSum F rest x
    + orderedOffDiagonalSum F rest

two : ℚ
two = 1ℚ + 1ℚ

columnEqualsRowForSymmetric :
  ∀ {A : Set}
    (F : A → A → ℚ) →
    ((x y : A) → F x y ≡ F y x) →
    (x : A) (rest : List A) →
  columnSum F rest x ≡ rowSum F x rest
columnEqualsRowForSymmetric F symmetric x [] = refl
columnEqualsRowForSymmetric F symmetric x (y ∷ rest) =
  cong₂ _+_
    (symmetric y x)
    (columnEqualsRowForSymmetric F symmetric x rest)

orderedOffDiagonalIsTwoUnordered :
  ∀ {A : Set}
    (F : A → A → ℚ) →
    ((x y : A) → F x y ≡ F y x) →
    (items : List A) →
  orderedOffDiagonalSum F items ≡ two * unorderedPairSum F items
orderedOffDiagonalIsTwoUnordered F symmetric [] = refl
orderedOffDiagonalIsTwoUnordered F symmetric (x ∷ rest)
  rewrite columnEqualsRowForSymmetric F symmetric x rest
        | orderedOffDiagonalIsTwoUnordered F symmetric rest =
  solve (rowSum F x rest ∷ unorderedPairSum F rest ∷ [])

round539FiniteSymmetricUnorderedOrderedIdentityClosed : Bool
round539FiniteSymmetricUnorderedOrderedIdentityClosed = true

round539IntroducesCardinalityFactorBeyondOrientationTwo : Bool
round539IntroducesCardinalityFactorBeyondOrientationTwo = false

round539FiniteSymmetricUnorderedOrderedIdentityClosedIsTrue :
  round539FiniteSymmetricUnorderedOrderedIdentityClosed ≡ true
round539FiniteSymmetricUnorderedOrderedIdentityClosedIsTrue = refl
