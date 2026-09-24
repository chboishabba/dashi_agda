module DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact where

------------------------------------------------------------------------
-- REAL SEQUENCE LIMIT FROM A VANISHING ERROR MAJORANT
--
-- This isolates the generic completeness/topology principle from YM-specific
-- quadrature geometry.  Downstream modules prove concrete finite error bounds;
-- this principle converts a vanishing majorant into equality with the selected
-- real-sequence limit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record RealSequenceLimitByVanishingError : Set₁ where
  field
    limit : (Nat → ℝ) → ℝ

    limitCongruent : ∀ left right →
      (∀ n → left n ≡ right n) →
      limit left ≡ limit right

    Vanishes : (Nat → ℝ) → Set

    vanishesCongruent : ∀ left right →
      (∀ n → left n ≡ right n) →
      Vanishes left →
      Vanishes right

    limitFromVanishingError :
      ∀ (sequence : Nat → ℝ) (target : ℝ) (error : Nat → ℝ) →
      (∀ n → absℝ (target -ℝ sequence n) ≤ℝ error n) →
      Vanishes error →
      limit sequence ≡ target

open RealSequenceLimitByVanishingError public

realSequenceLimitByVanishingErrorLevel : ProofLevel
realSequenceLimitByVanishingErrorLevel = standardImported
