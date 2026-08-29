module DASHI.Foundations.BishopNatSquareRootApproximationExact where

------------------------------------------------------------------------
-- NATURAL SQUARE ROOT AS A REGULAR RATIONAL INTERVAL APPROXIMATION
--
-- Built on the exact `vendor/bishop` Real.mkℝ constructor via
-- BishopRegularRationalApproximationExact.
--
-- For a natural radicand N, an approximation a_n is required to satisfy
--
--   0 <= a_n,
--   a_n^2 <= N,
--   N <= (a_n + 1/n)^2.
--
-- together with Bishop regularity.  These rational certificates are enough to
-- define the candidate Bishop real without introducing a postulated sqrt
-- operation.  Proving existence of such a canonical approximant family is the
-- remaining finite rational/Nat construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _+_; _*_; _≤_)

import Real as BishopReal

import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
import DASHI.Foundations.BishopRegularRationalApproximationExact as Approx
open import DASHI.Physics.YangMills.CompactLieProofLevel

natAsRational : Nat → ℚᵘ
natAsRational n = + n / 1

record BishopNatSquareRootApproximation (radicand : Nat) : Set₁ where
  field
    regularApproximation : Approx.BishopRegularRationalApproximation

    approximationNonnegative :
      (n : Nat) → .{{_ : NonZero n}} →
      0ℚᵘ ℚ.≤ Approx.approximation regularApproximation n

    approximationSquareBelowRadicand :
      (n : Nat) → .{{_ : NonZero n}} →
      (Approx.approximation regularApproximation n
        ℚ.* Approx.approximation regularApproximation n)
      ℚ.≤ natAsRational radicand

    radicandBelowOneOverNUpperSquare :
      (n : Nat) → .{{_ : NonZero n}} →
      natAsRational radicand
      ℚ.≤
      ((Approx.approximation regularApproximation n ℚ.+ (+ 1 / n))
        ℚ.*
       (Approx.approximation regularApproximation n ℚ.+ (+ 1 / n)))

open BishopNatSquareRootApproximation public

bishopNatSquareRootCandidate :
  ∀ {radicand : Nat} →
  BishopNatSquareRootApproximation radicand →
  BishopReal.ℝ
bishopNatSquareRootCandidate dataSet =
  Approx.realizeRegularApproximation
    (regularApproximation dataSet)

bishopNatSquareRootCandidateSequence :
  ∀ {radicand : Nat}
    (dataSet : BishopNatSquareRootApproximation radicand)
    (n : Nat) →
  BishopReal.seq (bishopNatSquareRootCandidate dataSet) n
  ≡ Approx.approximation (regularApproximation dataSet) n
bishopNatSquareRootCandidateSequence dataSet n = refl

bishopNatSquareRootRealizationLevel : ProofLevel
bishopNatSquareRootRealizationLevel = machineChecked

------------------------------------------------------------------------
-- Frontier:
--   construct the canonical rational approximant family for each Nat radicand
--   and prove the interval + regularity certificates above.
--
-- Once inhabited, the candidate is an actual Bishop real supplied by the
-- vendored constructor, not an abstract sqrt socket.
------------------------------------------------------------------------
