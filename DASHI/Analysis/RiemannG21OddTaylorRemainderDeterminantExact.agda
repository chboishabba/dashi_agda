module DASHI.Analysis.RiemannG21OddTaylorRemainderDeterminantExact where

------------------------------------------------------------------------
-- Exact determinant-level remainder decomposition for the odd G21 minor.
--
-- Let T_y(r) be the six-scaled cubic truncation
--
--   T_y(r) = -6 r N1(y) + r^3 N3(y),
--
-- and let E_y(r) be the corresponding six-scaled analytic remainder.  The
-- actual response is A_y(r)=T_y(r)+E_y(r).
--
-- For two heights a,p and radii r1,r2,
--
--   det A - det T
--
-- is exactly the sum of six structured remainder terms:
--
--   T_a1 E_p2 + E_a1 T_p2 + E_a1 E_p2
-- - T_a2 E_p1 - E_a2 T_p1 - E_a2 E_p1.
--
-- This is the quantity to bound directly against the strict cubic determinant
-- margin.  No independent approximation of the four determinant entries is
-- required by this owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

actualResponse : ℚ → ℚ → ℚ
actualResponse trunc remainder = trunc + remainder

det2 : ℚ → ℚ → ℚ → ℚ → ℚ
det2 a1 a2 p1 p2 = a1 * p2 - a2 * p1

actualOddDeterminant :
  ℚ → ℚ → ℚ → ℚ →
  ℚ → ℚ → ℚ → ℚ →
  ℚ
actualOddDeterminant ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 =
  det2
    (actualResponse ta1 ea1)
    (actualResponse ta2 ea2)
    (actualResponse tp1 ep1)
    (actualResponse tp2 ep2)

truncatedOddDeterminant : ℚ → ℚ → ℚ → ℚ → ℚ
truncatedOddDeterminant ta1 ta2 tp1 tp2 = det2 ta1 ta2 tp1 tp2

structuredRemainderError :
  ℚ → ℚ → ℚ → ℚ →
  ℚ → ℚ → ℚ → ℚ →
  ℚ
structuredRemainderError ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 =
    ta1 * ep2
  + ea1 * tp2
  + ea1 * ep2
  - ta2 * ep1
  - ea2 * tp1
  - ea2 * ep1

oddDeterminantRemainderDecomposition :
  (ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 : ℚ) →
  actualOddDeterminant ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2
  ≡
  truncatedOddDeterminant ta1 ta2 tp1 tp2
  + structuredRemainderError ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2
oddDeterminantRemainderDecomposition ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 =
  solve (ta1 ∷ ta2 ∷ tp1 ∷ tp2 ∷ ea1 ∷ ea2 ∷ ep1 ∷ ep2 ∷ [])

oddDeterminantErrorIdentity :
  (ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 : ℚ) →
  actualOddDeterminant ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2
  - truncatedOddDeterminant ta1 ta2 tp1 tp2
  ≡
  structuredRemainderError ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2
oddDeterminantErrorIdentity ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 =
  solve (ta1 ∷ ta2 ∷ tp1 ∷ tp2 ∷ ea1 ∷ ea2 ∷ ep1 ∷ ep2 ∷ [])

record OddRemainderDeterminantBudget : Set₁ where
  field
    Scalar : Set
    cubicMargin determinantError : Scalar
    StrictPositive : Scalar → Set
    StrictBelow : Scalar → Scalar → Set

    cubicMarginPositive : StrictPositive cubicMargin
    directStructuredRemainderBelowMargin :
      StrictBelow determinantError cubicMargin

    budgetReading : String

record OddTaylorRemainderBoundary : Set where
  constructor oddTaylorRemainderBoundary
  field
    exactSixTermDeterminantErrorDerived : Bool
    exactSixTermDeterminantErrorDerivedIsTrue :
      exactSixTermDeterminantErrorDerived ≡ true
    fourIndependentEntryErrorsRequired : Bool
    fourIndependentEntryErrorsRequiredIsFalse :
      fourIndependentEntryErrorsRequired ≡ false
    actualRemainderMagnitudeBoundDerived : Bool
    actualRemainderMagnitudeBoundDerivedIsFalse :
      actualRemainderMagnitudeBoundDerived ≡ false

canonicalOddTaylorRemainderBoundary : OddTaylorRemainderBoundary
canonicalOddTaylorRemainderBoundary =
  oddTaylorRemainderBoundary true refl false refl false refl
