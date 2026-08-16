module DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / INTERVAL REFERENCE
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- The previous Brillouin-box carrier hard-coded
--
--      lower = numeratorLower / denominatorUpper
--      upper = numeratorUpper / denominatorLower
--
-- for a strictly positive denominator interval. Those endpoints are correct
-- only when the numerator interval is nonnegative. Division by a positive
-- interval is monotone in the numerator but changes monotonicity in the
-- denominator with the SIGN of the numerator.
--
-- This finite sign split makes the endpoint choice explicit:
--
--   nL >= 0:       [ nL/dU , nU/dL ]
--   nU <= 0:       [ nL/dL , nU/dU ]
--   nL <= 0 <= nU: [ nL/dL , nU/dL ].
--
-- Sound division still requires the evaluator to prove 0 < dL and that the
-- numerator/denominator functions lie in their boxes. What is removed here
-- is the unsound assumption that the same denominator endpoint works for all
-- numerator signs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data NumeratorSignCase (lower upper : ℚ) : Set where
  numeratorNonnegative : 0ℚ ≤ lower → NumeratorSignCase lower upper
  numeratorNonpositive : upper ≤ 0ℚ → NumeratorSignCase lower upper
  numeratorStraddlesZero :
    lower ≤ 0ℚ → 0ℚ ≤ upper → NumeratorSignCase lower upper

quotientLowerEndpoint :
  ∀ {numeratorLower numeratorUpper} →
  NumeratorSignCase numeratorLower numeratorUpper →
  ℚ → ℚ → ℚ
quotientLowerEndpoint {numeratorLower}
    (numeratorNonnegative _) denominatorLower denominatorUpper =
  numeratorLower / denominatorUpper
quotientLowerEndpoint {numeratorLower}
    (numeratorNonpositive _) denominatorLower denominatorUpper =
  numeratorLower / denominatorLower
quotientLowerEndpoint {numeratorLower}
    (numeratorStraddlesZero _ _) denominatorLower denominatorUpper =
  numeratorLower / denominatorLower

quotientUpperEndpoint :
  ∀ {numeratorLower numeratorUpper} →
  NumeratorSignCase numeratorLower numeratorUpper →
  ℚ → ℚ → ℚ
quotientUpperEndpoint {numeratorUpper}
    (numeratorNonnegative _) denominatorLower denominatorUpper =
  numeratorUpper / denominatorLower
quotientUpperEndpoint {numeratorUpper}
    (numeratorNonpositive _) denominatorLower denominatorUpper =
  numeratorUpper / denominatorUpper
quotientUpperEndpoint {numeratorUpper}
    (numeratorStraddlesZero _ _) denominatorLower denominatorUpper =
  numeratorUpper / denominatorLower

positiveNumeratorLegacyLowerExact :
  ∀ numeratorLower numeratorUpper denominatorLower denominatorUpper
    (nonnegative : 0ℚ ≤ numeratorLower) →
  quotientLowerEndpoint
    (numeratorNonnegative {numeratorLower} {numeratorUpper} nonnegative)
    denominatorLower denominatorUpper
  ≡ numeratorLower / denominatorUpper
positiveNumeratorLegacyLowerExact numeratorLower numeratorUpper
    denominatorLower denominatorUpper nonnegative = refl

positiveNumeratorLegacyUpperExact :
  ∀ numeratorLower numeratorUpper denominatorLower denominatorUpper
    (nonnegative : 0ℚ ≤ numeratorLower) →
  quotientUpperEndpoint
    (numeratorNonnegative {numeratorLower} {numeratorUpper} nonnegative)
    denominatorLower denominatorUpper
  ≡ numeratorUpper / denominatorLower
positiveNumeratorLegacyUpperExact numeratorLower numeratorUpper
    denominatorLower denominatorUpper nonnegative = refl

positiveDenominatorSignAwareEndpointSelectionLevel : ProofLevel
positiveDenominatorSignAwareEndpointSelectionLevel = machineChecked
