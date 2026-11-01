module DASHI.Core.KernelMonoid where

open import DASHI.Core.Prelude

-- Generic kernel as endomorphism.
record Kernel (S : Set) : Set where
  field K : S → S

_∘K_ : ∀ {S} → Kernel S → Kernel S → Kernel S
_∘K_ {S} A B = record { K = λ x → Kernel.K A (Kernel.K B x) }

idK : ∀ {S} → Kernel S
idK = record { K = λ x → x }

-- Extensional equality for kernels (needed to state laws).
KernelEq : ∀ {S} → Kernel S → Kernel S → Set
KernelEq {S} A B = ∀ x → Kernel.K A x ≡ Kernel.K B x

compose-assoc :
  ∀ {S} (A B C : Kernel S) →
  KernelEq ((A ∘K B) ∘K C) (A ∘K (B ∘K C))
compose-assoc A B C x = refl

left-id : ∀ {S} (A : Kernel S) → KernelEq (idK ∘K A) A
left-id A x = refl

right-id : ∀ {S} (A : Kernel S) → KernelEq (A ∘K idK) A
right-id A x = refl
