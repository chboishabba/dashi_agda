module DASHI.Codec.DNAProductionNormalization where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Core.Prelude using (_×_; _,_)

second : ∀ {X Y : Set} → X × Y → Y
second (x , y) = y

record NormalizationKernel : Set₁ where
  field
    State : Set
    Output : Set
    needsNormalization : State → Bool
    normalizeStep : State → Output × State
open NormalizationKernel public

data NormalizationResult (K : NormalizationKernel) : Nat → State K → Set where
  normalized :
    ∀ {fuel s} →
    needsNormalization K s ≡ false →
    NormalizationResult K fuel s

  exhausted :
    ∀ {s} →
    needsNormalization K s ≡ true →
    NormalizationResult K zero s

  emitted :
    ∀ {fuel s} →
    needsNormalization K s ≡ true →
    NormalizationResult K fuel (second (normalizeStep K s)) →
    NormalizationResult K (suc fuel) s

normalizeWithFuel :
  (K : NormalizationKernel) →
  (fuel : Nat) →
  (s : State K) →
  NormalizationResult K fuel s
normalizeWithFuel K zero s with needsNormalization K s
... | false = normalized refl
... | true = exhausted refl
normalizeWithFuel K (suc fuel) s with needsNormalization K s
... | false = normalized refl
... | true = emitted refl (normalizeWithFuel K fuel (second (normalizeStep K s)))

normalization-terminates-by-fuel :
  (K : NormalizationKernel) →
  (fuel : Nat) →
  (s : State K) →
  Σ (NormalizationResult K fuel s) (λ result → result ≡ result)
normalization-terminates-by-fuel K fuel s =
  normalizeWithFuel K fuel s , refl

record NormalizedCoderReceipt : Set₁ where
  field
    kernel : NormalizationKernel
    reachable : State kernel → Set
    budget : State kernel → Nat
    invariant : State kernel → Set
    stepPreservesInvariant :
      ∀ s → invariant s → invariant (second (normalizeStep kernel s))
    budgetSuffices :
      ∀ s → reachable s →
      NormalizationResult kernel (budget s) s
