module DASHI.Physics.Closure.Basin where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

-- Minimal eventual reachability surface for attractor-relative reasoning.
data Eventually {ℓ : Level} {Carrier : Set ℓ}
  (step : Carrier → Carrier)
  (StableShell : Carrier → Set ℓ)
  : Carrier → Set ℓ where
  now : ∀ {x} → StableShell x → Eventually step StableShell x
  later : ∀ {x} → Eventually step StableShell (step x) → Eventually step StableShell x

-- Basin carried directly on the projected observable space. This keeps the
-- contract tied to an explicit attractor-relative object rather than a raw
-- Boolean/predicate.
record Basin
  {ℓ : Level}
  (Source : Set ℓ)
  : Set (lsuc ℓ) where
  field
    step : Source → Source
    StableShell : Source → Set ℓ
    InBasin : Source → Set ℓ

    basin-eventually-stable :
      ∀ x → InBasin x → Eventually step StableShell x

    basin-step :
      ∀ x → InBasin x → InBasin (step x)

open Basin public
