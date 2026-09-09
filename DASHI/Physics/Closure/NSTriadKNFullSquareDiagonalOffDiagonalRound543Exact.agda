module DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact where

------------------------------------------------------------------------
-- ROUND543 / GENERIC FULL SQUARE = DIAGONAL + ORDERED OFF-DIAGONAL
--
-- R540 moves the literal unordered R406 pair sum onto an ordered off-diagonal
-- carrier.  The complete output fibre is swap-stable, so the next useful
-- carrier is the full ordered square.  This file isolates exactly what is added:
-- the diagonal and nothing else.
--
-- For any finite list xs and any rational pair scalar F,
--
--   Full(F,xs) = Diag(F,xs) + OffDiagOrdered(F,xs).
--
-- No symmetry assumption, sign estimate, norm, or Navier--Stokes theorem is
-- used.  This is finite list algebra only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539

fullSquareSum :
  ∀ {A : Set} → (A → A → ℚ) → List A → ℚ
fullSquareSum F [] = 0ℚ
fullSquareSum F (x ∷ rest) =
  F x x
  + R539.rowSum F x rest
  + R539.columnSum F rest x
  + fullSquareSum F rest

diagonalSum :
  ∀ {A : Set} → (A → A → ℚ) → List A → ℚ
diagonalSum F [] = 0ℚ
diagonalSum F (x ∷ rest) = F x x + diagonalSum F rest

fullSquareIsDiagonalPlusOrderedOffDiagonal :
  ∀ {A : Set}
    (F : A → A → ℚ) →
    (items : List A) →
  fullSquareSum F items
  ≡ diagonalSum F items + R539.orderedOffDiagonalSum F items
fullSquareIsDiagonalPlusOrderedOffDiagonal F [] = refl
fullSquareIsDiagonalPlusOrderedOffDiagonal F (x ∷ rest)
  rewrite fullSquareIsDiagonalPlusOrderedOffDiagonal F rest =
  solve
    (F x x
      ∷ R539.rowSum F x rest
      ∷ R539.columnSum F rest x
      ∷ diagonalSum F rest
      ∷ R539.orderedOffDiagonalSum F rest
      ∷ [])

round543FullSquareDiagonalSplitClosed : Bool
round543FullSquareDiagonalSplitClosed = true

round543IntroducesAnyAnalyticEstimate : Bool
round543IntroducesAnyAnalyticEstimate = false

round543DiagonalAutomaticallyZero : Bool
round543DiagonalAutomaticallyZero = false

round543FullSquareDiagonalSplitClosedIsTrue :
  round543FullSquareDiagonalSplitClosed ≡ true
round543FullSquareDiagonalSplitClosedIsTrue = refl

round543IntroducesAnyAnalyticEstimateIsFalse :
  round543IntroducesAnyAnalyticEstimate ≡ false
round543IntroducesAnyAnalyticEstimateIsFalse = refl

round543DiagonalAutomaticallyZeroIsFalse :
  round543DiagonalAutomaticallyZero ≡ false
round543DiagonalAutomaticallyZeroIsFalse = refl
