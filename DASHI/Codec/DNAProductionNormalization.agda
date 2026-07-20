module DASHI.Codec.DNAProductionNormalization where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Generic executable normalization kernel.
--
-- Arithmetic and rANS backends differ in their numeric state, but both use the
-- same proof pattern: each emitted normalization symbol consumes one unit of a
-- structurally decreasing budget. Concrete backends must additionally prove
-- that their chosen budget bounds every reachable normalization chain.

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
    where
    second : ∀ {X Y : Set} → X × Y → Y
    second (x , y) = y

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
  where
  second : ∀ {X Y : Set} → X × Y → Y
  second (x , y) = y

-- Structural termination theorem: normalization always produces a finite
-- result for every supplied budget. No general numeric bound is fabricated.
normalization-terminates-by-fuel :
  (K : NormalizationKernel) →
  (fuel : Nat) →
  (s : State K) →
  Σ (NormalizationResult K fuel s) (λ result → result ≡ result)
normalization-terminates-by-fuel K fuel s =
  normalizeWithFuel K fuel s , refl

------------------------------------------------------------------------
-- Backend receipt. A concrete arithmetic/rANS implementation supplies the
-- reachable-state budget theorem and interval/state invariants.

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
  where
  second : ∀ {X Y : Set} → X × Y → Y
  second (x , y) = y
