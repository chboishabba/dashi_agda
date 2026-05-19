module DASHI.Arithmetic.CancellationPressureRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat using (_+_; _≤_; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl; +-identityʳ)
open import Data.Product using (proj₁)

open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; residueDepth
  ; carryBudget
  ; padicDepth
  ; normalizeAddCanonical
  )
open import DASHI.Arithmetic.NormalizeAdd using
  ( normalizeAdd
  ; normalizeAdd-canonical
  )
open import DASHI.Arithmetic.CanonicalResidueZero using
  ( canonicalResidueBudget-fromCanonical )
open import DASHI.Arithmetic.CancellationPressureFromCanonical using
  ( StateSupportPressure )

RefinedCancellationPressure : NormalizeAddState → Nat
RefinedCancellationPressure s = residueDepth s + carryBudget s

canonicalResidueDepth-fromCanonical :
  ∀ s → normalizeAddCanonical s → residueDepth s ≡ padicDepth s
canonicalResidueDepth-fromCanonical _ canon = proj₁ canon

canonical⇒refinedBounded :
  ∀ s →
  normalizeAddCanonical s →
  RefinedCancellationPressure s ≤ StateSupportPressure s
canonical⇒refinedBounded s canon
  rewrite canonicalResidueBudget-fromCanonical s canon
        | NatP.+-identityʳ (residueDepth s)
        | canonicalResidueDepth-fromCanonical s canon
  = NatP.≤-refl

normalizeAdd⇒refinedBounded :
  ∀ s →
  RefinedCancellationPressure (normalizeAdd s)
    ≤
  StateSupportPressure (normalizeAdd s)
normalizeAdd⇒refinedBounded s =
  canonical⇒refinedBounded (normalizeAdd s) (normalizeAdd-canonical s)

record CancellationPressureRefinement : Set₁ where
  field
    refined : NormalizeAddState → Nat
    canonicalBound :
      ∀ s →
      normalizeAddCanonical s →
      refined s ≤ StateSupportPressure s
    normalizeAddOneStepBound :
      ∀ s →
      refined (normalizeAdd s) ≤
      StateSupportPressure (normalizeAdd s)

cancellationPressureRefinement : CancellationPressureRefinement
cancellationPressureRefinement = record
  { refined = RefinedCancellationPressure
  ; canonicalBound = canonical⇒refinedBounded
  ; normalizeAddOneStepBound = normalizeAdd⇒refinedBounded
  }
