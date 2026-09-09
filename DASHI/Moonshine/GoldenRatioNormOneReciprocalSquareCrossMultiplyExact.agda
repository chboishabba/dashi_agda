module DASHI.Moonshine.GoldenRatioNormOneReciprocalSquareCrossMultiplyExact where

------------------------------------------------------------------------
-- DENOMINATOR-CLEARED NORM-ONE -> RECIPROCAL-SQUARE WELD
--
-- For a positive Nat pair satisfying
--
--   p^2 = p q + q^2 + 1,
--
-- the rational identity
--
--   (p/q)^2 - p/q - 1 = 1/q^2
--
-- is equivalent after multiplication by q^2 to the original Nat equality.
-- This owner proves that exact denominator-cleared equality on every state of
-- the balanced-FRACTRAN macro sequence.  Lifting it through the vendored
-- rational embedding to Bishop equivalence remains a separate thin adapter.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANNormOneInvariantExact as Norm

------------------------------------------------------------------------
-- 1. Generic cross-multiplied polynomial identity.
------------------------------------------------------------------------

normOneCrossMultiply :
  (p q : Nat) →
  Norm.NormOne p q →
  p * p ≡ p * q + q * q + 1
normOneCrossMultiply p q norm = norm

-- Written in the exact arrangement obtained by clearing q^2 from
-- (p/q)^2 - p/q - 1 = 1/q^2:
--
--   p^2 = p q + q^2 + 1.
--
-- The separate theorem below makes explicit that no additional arithmetic
-- content is introduced by the reciprocal-square presentation.
reciprocalSquareClearedForm :
  (p q : Nat) →
  Norm.NormOne p q →
  p * p ≡ (p * q + q * q) + 1
reciprocalSquareClearedForm p q norm = norm

------------------------------------------------------------------------
-- 2. Every balanced-FRACTRAN macro state carries the cleared receipt.
------------------------------------------------------------------------

balancedMacroReciprocalSquareCleared :
  (n : Nat) →
  let pair = Ratio.iteratePositiveMacro n
      p = Ratio.positiveHi pair
      q = Ratio.positiveLo pair
  in
  p * p ≡ (p * q + q * q) + 1
balancedMacroReciprocalSquareCleared n =
  Norm.balancedMacroNormOne n

------------------------------------------------------------------------
-- 3. A field-solver-normalized companion identity.
--
-- Multiplying both sides of
--
--   r^2 - r - 1 = 1/q^2,  r=p/q,
--
-- by q^2 gives precisely the equation above.  The following polynomial
-- rearrangement is useful to the rational/Bishop adapter because it avoids
-- subtraction on Nat.
------------------------------------------------------------------------

clearedDefectBalance :
  (p q : Nat) →
  Norm.NormOne p q →
  p * p + q * q ≡ p * q + (q * q + q * q) + 1
clearedDefectBalance p q norm =
  trans
    (cong (λ x → x + q * q) norm)
    (solve 3
      (λ p q _ →
        ((((p :* q) :+ (q :* q)) :+ con 1) :+ (q :* q))
        :=
        ((p :* q) :+ ((q :* q) :+ (q :* q))) :+ con 1)
      refl p q 0)

------------------------------------------------------------------------
-- 4. Frontier.
------------------------------------------------------------------------

data ReciprocalSquareCrossMultiplyResidual : Set where
  missingUnnormalisedRationalEquivalenceLift : ReciprocalSquareCrossMultiplyResidual
  missingBishopEmbeddingEquivalenceLift : ReciprocalSquareCrossMultiplyResidual
  missingConjugateFactorLowerBound : ReciprocalSquareCrossMultiplyResidual
  missingFinalConvergence : ReciprocalSquareCrossMultiplyResidual

record ReciprocalSquareCrossMultiplyFrontier : Set where
  constructor reciprocal-square-cross-multiply-frontier
  field
    allMacroStatesNormOne : Bool
    denominatorClearedReciprocalSquareExact : Bool
    rationalEquivalenceLiftExact : Bool
    bishopEmbeddingLiftExact : Bool
    firstResidual : ReciprocalSquareCrossMultiplyResidual

canonicalReciprocalSquareCrossMultiplyFrontier :
  ReciprocalSquareCrossMultiplyFrontier
canonicalReciprocalSquareCrossMultiplyFrontier =
  reciprocal-square-cross-multiply-frontier
    true true false false
    missingUnnormalisedRationalEquivalenceLift
