module DASHI.Foundations.BishopRegularRationalApproximationExact where

------------------------------------------------------------------------
-- CONSTRUCT BISHOP REALS DIRECTLY FROM THE VENDORED `Real.mkℝ` INTERFACE
--
-- The repository carries viktorcsimma/bishop at `vendor/bishop`; see
-- BishopVendoredSubmoduleProvenanceExact.  At that pinned commit a real number
-- is a rational sequence equipped with the regularity estimate
--
--   |a_m - a_n| <= 1/m + 1/n.
--
-- This owner packages exactly that constructor shape so later analytic work
-- (notably square root for the Erdos partition bound) can supply rational
-- approximants without inventing another completion or real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base as Nat using (NonZero)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_; _+_; _-_; _≤_; ∣_∣)

import Real as BishopReal

import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
open import DASHI.Physics.YangMills.CompactLieProofLevel

record BishopRegularRationalApproximation : Set₁ where
  field
    approximation : Nat → ℚᵘ
    regular :
      (m n : Nat) →
      .{{_ : NonZero m}} →
      .{{_ : NonZero n}} →
      ℚ.∣ approximation m ℚ.- approximation n ∣
      ℚ.≤
      ((+ 1 / m) ℚ.+ (+ 1 / n))

open BishopRegularRationalApproximation public

realizeRegularApproximation :
  BishopRegularRationalApproximation → BishopReal.ℝ
realizeRegularApproximation dataSet =
  BishopReal.mkℝ
    (approximation dataSet)
    (regular dataSet)

realizedSequenceExact :
  (dataSet : BishopRegularRationalApproximation) →
  (n : Nat) →
  BishopReal.seq (realizeRegularApproximation dataSet) n
  ≡ approximation dataSet n
realizedSequenceExact dataSet n = refl

bishopRegularApproximationConstructionLevel : ProofLevel
bishopRegularApproximationConstructionLevel = machineChecked

------------------------------------------------------------------------
-- No convergence theorem is postulated here: `realizeRegularApproximation`
-- is literally the constructor exported by the pinned Bishop submodule.
------------------------------------------------------------------------
