module DASHI.Physics.Closure.NSTriadKNHHBadCrossingVariationCostRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Turn the reachability/entry-count idea into the exact finite theorem needed
-- by the HH-bad lane.  A bad crossing carries a realized positive variation
-- jump j and a common hysteretic minimum delta with
--
--   delta <= j.
--
-- Summing over the actual crossing list gives
--
--   delta + ... + delta <= sum crossing jumps.
--
-- If those jumps are themselves charged to the positive variation of the
-- directional defect, then
--
--   repeatedCost delta crossings <= positiveVariation.
--
-- `repeatedCost` is the constructive finite form of N_bad * delta; no Nat-to-
-- real coercion and no informal crossing count are needed.  The remaining
-- physical theorem is to instantiate each actual HH-bad entrance with such a
-- hysteretic jump and prove the cutoff-uniform positive-variation bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

record BadCrossing (minimumJump : ℚ) : Set where
  constructor bad-crossing
  field
    realizedJump : ℚ
    minimumJumpPaid : minimumJump ≤ realizedJump

open BadCrossing public

repeatedCost : ℚ → ∀ {dummy : Set} → List dummy → ℚ
repeatedCost minimumJump [] = 0ℚ
repeatedCost minimumJump (_ ∷ rest) =
  minimumJump + repeatedCost minimumJump rest

sumCrossingJumps : ∀ {minimumJump} → List (BadCrossing minimumJump) → ℚ
sumCrossingJumps [] = 0ℚ
sumCrossingJumps (crossing ∷ rest) =
  realizedJump crossing + sumCrossingJumps rest

crossingMinimumCostBound :
  ∀ {minimumJump} (crossings : List (BadCrossing minimumJump)) →
  repeatedCost minimumJump crossings ≤ sumCrossingJumps crossings
crossingMinimumCostBound [] = ℚP.≤-refl
crossingMinimumCostBound (crossing ∷ rest) =
  ℚP.+-mono-≤
    (minimumJumpPaid crossing)
    (crossingMinimumCostBound rest)

record PositiveVariationCharge
    {minimumJump : ℚ}
    (crossings : List (BadCrossing minimumJump)) : Set where
  constructor positive-variation-charge
  field
    positiveVariation : ℚ
    crossingJumpsBelowPositiveVariation :
      sumCrossingJumps crossings ≤ positiveVariation

open PositiveVariationCharge public

hystereticCrossingCostBound :
  ∀ {minimumJump crossings} →
  (charge : PositiveVariationCharge {minimumJump} crossings) →
  repeatedCost minimumJump crossings ≤ positiveVariation charge
hystereticCrossingCostBound {crossings = crossings} charge =
  ℚP.≤-trans
    (crossingMinimumCostBound crossings)
    (crossingJumpsBelowPositiveVariation charge)

record PhysicalHHBadCrossingData : Set₁ where
  field
    minimumHysteresisJump : ℚ
    actualCrossings : List (BadCrossing minimumHysteresisJump)
    actualPositiveVariationCharge :
      PositiveVariationCharge actualCrossings

open PhysicalHHBadCrossingData public

physicalHHBadCrossingCost :
  (dataSet : PhysicalHHBadCrossingData) →
  repeatedCost
    (minimumHysteresisJump dataSet)
    (actualCrossings dataSet)
  ≤ positiveVariation (actualPositiveVariationCharge dataSet)
physicalHHBadCrossingCost dataSet =
  hystereticCrossingCostBound (actualPositiveVariationCharge dataSet)

hhBadCrossingVariationAlgebraClosed : Bool
hhBadCrossingVariationAlgebraClosed = true

physicalPositiveVariationBoundConstructed : Bool
physicalPositiveVariationBoundConstructed = false

hhBadCrossingVariationAlgebraClosedIsTrue :
  hhBadCrossingVariationAlgebraClosed ≡ true
hhBadCrossingVariationAlgebraClosedIsTrue = refl

physicalPositiveVariationBoundConstructedIsFalse :
  physicalPositiveVariationBoundConstructed ≡ false
physicalPositiveVariationBoundConstructedIsFalse = refl
