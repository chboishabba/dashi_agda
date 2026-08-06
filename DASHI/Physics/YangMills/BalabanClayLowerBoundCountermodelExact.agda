module DASHI.Physics.YangMills.BalabanClayLowerBoundCountermodelExact where

------------------------------------------------------------------------
-- SOURCE STRESS TEST
--
-- Henry Watt, "The Yang-Mills Mass Gap: From Proof Attempts to Dissolution
-- by Recontextualisation", WCCC Principia, Document 35 v12 (2026).
-- No DOI recorded.
--
-- The paper's factor-of-23 calculation is useful as a diagnostic of a weak
-- lower bound.  The theorem below closes the exact logical point: a sequence
-- of certified lower bounds may vanish while the quantities being bounded
-- remain uniformly positive.  Therefore failure of a lower bound in physical
-- units is not a proof that the physical gap vanishes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

infix 4 _≤ᴺ_
data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ᴺ n
  suc≤suc : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

one : Nat
one = suc zero

vanishingCertifiedLowerBound : Nat → Nat
vanishingCertifiedLowerBound stage = zero

uniformPositivePhysicalGap : Nat → Nat
uniformPositivePhysicalGap stage = one

certifiedLowerBoundIsValid : ∀ stage →
  vanishingCertifiedLowerBound stage ≤ᴺ uniformPositivePhysicalGap stage
certifiedLowerBoundIsValid stage = zero≤

certifiedLowerBoundVanishesAtEveryStage : ∀ stage →
  vanishingCertifiedLowerBound stage ≡ zero
certifiedLowerBoundVanishesAtEveryStage stage = refl

physicalGapRemainsOneAtEveryStage : ∀ stage →
  uniformPositivePhysicalGap stage ≡ one
physicalGapRemainsOneAtEveryStage stage = refl

physicalGapUniformlyPositive : ∀ stage →
  one ≤ᴺ uniformPositivePhysicalGap stage
physicalGapUniformlyPositive stage = suc≤suc zero≤

record VanishingBoundPositiveQuantityCountermodel : Set where
  field
    lowerBound actualQuantity : Nat → Nat
    lowerBoundValid : ∀ stage → lowerBound stage ≤ᴺ actualQuantity stage
    lowerBoundVanishes : ∀ stage → lowerBound stage ≡ zero
    actualUniformlyPositive : ∀ stage → one ≤ᴺ actualQuantity stage

open VanishingBoundPositiveQuantityCountermodel public

factorMismatchCountermodel : VanishingBoundPositiveQuantityCountermodel
factorMismatchCountermodel = record
  { lowerBound = vanishingCertifiedLowerBound
  ; actualQuantity = uniformPositivePhysicalGap
  ; lowerBoundValid = certifiedLowerBoundIsValid
  ; lowerBoundVanishes = certifiedLowerBoundVanishesAtEveryStage
  ; actualUniformlyPositive = physicalGapUniformlyPositive
  }

vanishingLowerBoundDoesNotDeterminePhysicalGapLevel : ProofLevel
vanishingLowerBoundDoesNotDeterminePhysicalGapLevel = machineChecked
