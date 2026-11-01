module DASHI.Physics.Closure.NSTriadKNSymmetrizedHalfUnorderedOrderedExact where

------------------------------------------------------------------------
-- GENERIC FINITE TRANSPOSE COMPLETION
--
-- For any rational pair kernel H on a finite list, define
--
--   S(x,y) = 1/2 * (H(x,y) + H(y,x)).
--
-- Then the unordered position-pair sum of S is exactly one half of the ordered
-- off-diagonal sum of H:
--
--   sum_{i<j} S(x_i,x_j) = 1/2 * sum_{i != j} H(x_i,x_j).
--
-- No symmetry assumption on H is required.  This is the finite combinatorial
-- compiler needed to recognize a second product-rule/adjoint channel as the
-- transpose completion of the first rather than as an independent analytic
-- obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539

half : ℚ
half = + 1 / 2

symmetrizedHalf :
  ∀ {A : Set} → (A → A → ℚ) → A → A → ℚ
symmetrizedHalf H x y = half * (H x y + H y x)

rowSymmetrizedHalf :
  ∀ {A : Set}
    (H : A → A → ℚ) →
    (x : A) →
    (rest : List A) →
  R539.rowSum (symmetrizedHalf H) x rest
  ≡ half *
      (R539.rowSum H x rest + R539.columnSum H rest x)
rowSymmetrizedHalf H x [] = solve []
rowSymmetrizedHalf H x (y ∷ rest)
    rewrite rowSymmetrizedHalf H x rest =
  solve
    ( H x y
    ∷ H y x
    ∷ R539.rowSum H x rest
    ∷ R539.columnSum H rest x
    ∷ [])

unorderedSymmetrizedHalfIsHalfOrderedOffDiagonal :
  ∀ {A : Set}
    (H : A → A → ℚ) →
    (items : List A) →
  R539.unorderedPairSum (symmetrizedHalf H) items
  ≡ half * R539.orderedOffDiagonalSum H items
unorderedSymmetrizedHalfIsHalfOrderedOffDiagonal H [] = solve []
unorderedSymmetrizedHalfIsHalfOrderedOffDiagonal H (x ∷ rest)
    rewrite rowSymmetrizedHalf H x rest
          | unorderedSymmetrizedHalfIsHalfOrderedOffDiagonal H rest =
  solve
    ( R539.rowSum H x rest
    ∷ R539.columnSum H rest x
    ∷ R539.orderedOffDiagonalSum H rest
    ∷ [])

record SymmetrizedHalfBoundary : Set where
  constructor symmetrized-half-boundary
  field
    unorderedSymmetrizedPairIsHalfOrderedKernel : Bool
    requiresKernelSymmetry : Bool
    introducesNorm : Bool
    introducesAbsoluteValue : Bool

canonicalSymmetrizedHalfBoundary : SymmetrizedHalfBoundary
canonicalSymmetrizedHalfBoundary =
  symmetrized-half-boundary true false false false
