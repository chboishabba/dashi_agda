module DASHI.Arithmetic.NormalizeAddSumPreservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)
open import Data.Unit using (⊤; tt)

open import DASHI.TrackedPrimes using (SSP; toNat)
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (vp)
open import DASHI.Arithmetic.NormalizeAdd using (normalizeAdd)
open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; lhs
  ; rhs
  )

------------------------------------------------------------------------
-- HEP-R54a / W2 nearest positive invariant.
--
-- The current `normalizeAdd` implementation does not rewrite `lhs` or `rhs`;
-- it resolves residue/carry bookkeeping fields.  Therefore the observable
-- sum `lhs + rhs` is definitionally preserved.  The p-adic valuation of that
-- sum is preserved for every tracked prime by the same definitional equality.
--
-- This is a theorem-level positive ingredient.  It is intentionally not a
-- W2 kill receipt by itself: the existing W2 promotion surface still requires
-- the constructorless promotion authority token and carrier-general rate
-- receipt.

normalizeAdd-sumPreserved :
  ∀ s →
  lhs (normalizeAdd s) + rhs (normalizeAdd s)
  ≡
  lhs s + rhs s
normalizeAdd-sumPreserved _ = refl

vpSumInvariant :
  ∀ p s →
  vp p (lhs (normalizeAdd s) + rhs (normalizeAdd s))
  ≡
  vp p (lhs s + rhs s)
vpSumInvariant _ _ = refl

trackedPrimeVpSumInvariant :
  ∀ p s →
  vp (toNat p) (lhs (normalizeAdd s) + rhs (normalizeAdd s))
  ≡
  vp (toNat p) (lhs s + rhs s)
trackedPrimeVpSumInvariant _ _ = refl

normalizeAddOneStepSumInvariantEvidence : Set
normalizeAddOneStepSumInvariantEvidence = ⊤

normalizeAddOneStepSumInvariantWitness :
  normalizeAddOneStepSumInvariantEvidence
normalizeAddOneStepSumInvariantWitness = tt

record NormalizeAddSumPreservationReceipt : Set₁ where
  field
    State :
      Set

    step :
      State → State

    sumObservable :
      State → Nat

    sumPreserved :
      ∀ s → sumObservable (step s) ≡ sumObservable s

    pAdicSumInvariant :
      ∀ p s →
      vp p (sumObservable (step s))
      ≡
      vp p (sumObservable s)

    trackedPrimeInvariant :
      ∀ p s →
      vp (toNat p) (sumObservable (step s))
      ≡
      vp (toNat p) (sumObservable s)

    nonPromotionBoundary :
      Set

canonicalNormalizeAddSumPreservationReceipt :
  NormalizeAddSumPreservationReceipt
canonicalNormalizeAddSumPreservationReceipt =
  record
    { State =
        NormalizeAddState
    ; step =
        normalizeAdd
    ; sumObservable =
        λ s → lhs s + rhs s
    ; sumPreserved =
        normalizeAdd-sumPreserved
    ; pAdicSumInvariant =
        vpSumInvariant
    ; trackedPrimeInvariant =
        trackedPrimeVpSumInvariant
    ; nonPromotionBoundary =
        normalizeAddOneStepSumInvariantEvidence
    }
