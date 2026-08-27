module DASHI.Analysis.RiemannG21OddTaylorDeterminantExact where

------------------------------------------------------------------------
-- Exact cubic-truncation factorization for the G21 odd parity minor.
--
-- Write the odd response schematically as
--
--   B_y(r) = - r N1(y) + r^3 N3(y)/6 + R_y(r).
--
-- To avoid division in the algebraic core, define the six-times truncated
-- response
--
--   T_y(r) = -6 r N1(y) + r^3 N3(y).
--
-- Then the 2x2 determinant of the truncated responses factors exactly as
--
--   det T =
--     6 r1 r2 (r2^2-r1^2)
--       * (N3(a) N1(p) - N1(a) N3(p)).
--
-- Equivalently, if the strict TP2 continuum margin is oriented as
--
--   Delta = N1(a) N3(p) - N3(a) N1(p) > 0,
--
-- then
--
--   det T = - 6 r1 r2 (r2^2-r1^2) Delta.
--
-- The linear-linear contribution and cubic-cubic contribution cancel
-- identically before any estimate.  This is the determinant-level Taylor
-- structure that the remainder analysis should preserve.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

square : ℚ → ℚ
square x = x * x

cube : ℚ → ℚ
cube x = x * x * x

oddCubicScaled : ℚ → ℚ → ℚ → ℚ
oddCubicScaled r n1 n3 =
  (0 - ((6 * r) * n1)) + cube r * n3

oddCubicDeterminant :
  ℚ → ℚ →
  ℚ → ℚ →
  ℚ → ℚ →
  ℚ
oddCubicDeterminant r1 r2 n1a n3a n1p n3p =
  oddCubicScaled r1 n1a n3a * oddCubicScaled r2 n1p n3p
  -
  oddCubicScaled r2 n1a n3a * oddCubicScaled r1 n1p n3p

oddMomentPositiveMargin : ℚ → ℚ → ℚ → ℚ → ℚ
oddMomentPositiveMargin n1a n3a n1p n3p =
  n1a * n3p - n3a * n1p

oddCubicDeterminantFactorization :
  (r1 r2 n1a n3a n1p n3p : ℚ) →
  oddCubicDeterminant r1 r2 n1a n3a n1p n3p
  ≡
  (6 * r1 * r2 * (square r2 - square r1))
    * (n3a * n1p - n1a * n3p)
oddCubicDeterminantFactorization r1 r2 n1a n3a n1p n3p =
  solve (r1 ∷ r2 ∷ n1a ∷ n3a ∷ n1p ∷ n3p ∷ [])

oddCubicDeterminantAsNegativeMargin :
  (r1 r2 n1a n3a n1p n3p : ℚ) →
  oddCubicDeterminant r1 r2 n1a n3a n1p n3p
  ≡
  (0 - (6 * r1 * r2 * (square r2 - square r1)))
    * oddMomentPositiveMargin n1a n3a n1p n3p
oddCubicDeterminantAsNegativeMargin r1 r2 n1a n3a n1p n3p =
  solve (r1 ∷ r2 ∷ n1a ∷ n3a ∷ n1p ∷ n3p ∷ [])

linearPartScaled : ℚ → ℚ → ℚ
linearPartScaled r n1 = 0 - ((6 * r) * n1)

cubicPart : ℚ → ℚ → ℚ
cubicPart r n3 = cube r * n3

linearLinearCancellation :
  (r1 r2 n1a n1p : ℚ) →
  linearPartScaled r1 n1a * linearPartScaled r2 n1p
  ≡
  linearPartScaled r2 n1a * linearPartScaled r1 n1p
linearLinearCancellation r1 r2 n1a n1p =
  solve (r1 ∷ r2 ∷ n1a ∷ n1p ∷ [])

cubicCubicCancellation :
  (r1 r2 n3a n3p : ℚ) →
  cubicPart r1 n3a * cubicPart r2 n3p
  ≡
  cubicPart r2 n3a * cubicPart r1 n3p
cubicCubicCancellation r1 r2 n3a n3p =
  solve (r1 ∷ r2 ∷ n3a ∷ n3p ∷ [])

record OddTaylorDeterminantBoundary : Set where
  constructor oddTaylorDeterminantBoundary
  field
    cubicDeterminantFactorizationDerived : Bool
    cubicDeterminantFactorizationDerivedIsTrue :
      cubicDeterminantFactorizationDerived ≡ true
    linearLinearCancellationDerived : Bool
    linearLinearCancellationDerivedIsTrue :
      linearLinearCancellationDerived ≡ true
    cubicCubicCancellationDerived : Bool
    cubicCubicCancellationDerivedIsTrue :
      cubicCubicCancellationDerived ≡ true
    strictSignFromOrderedRadiiAndMarginDerived : Bool
    strictSignFromOrderedRadiiAndMarginDerivedIsFalse :
      strictSignFromOrderedRadiiAndMarginDerived ≡ false
    actualAnalyticRemainderBoundDerived : Bool
    actualAnalyticRemainderBoundDerivedIsFalse :
      actualAnalyticRemainderBoundDerived ≡ false

canonicalOddTaylorDeterminantBoundary : OddTaylorDeterminantBoundary
canonicalOddTaylorDeterminantBoundary =
  oddTaylorDeterminantBoundary
    true refl true refl true refl false refl false refl
