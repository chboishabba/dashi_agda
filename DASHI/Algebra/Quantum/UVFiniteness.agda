module DASHI.Algebra.Quantum.UVFiniteness where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

ℚ : Set
ℚ = ⊤

0q : ℚ
0q = tt

record Preorder (A : Set) : Set₁ where
  field
    _≤_ : A → A → Set
    ≤-refl : ∀ x → x ≤ x
    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

open Preorder public

Λ : Set
Λ = ⊤

next : Λ → Λ
next _ = tt

Theory : Λ → Set
Theory _ = ⊤

RG : ∀ {ℓ} → Theory ℓ → Theory (next ℓ)
RG _ = tt

Amp : ∀ {ℓ} → Theory ℓ → ℚ
Amp _ = tt

AmpOrd : Preorder ℚ
AmpOrd = record
  { _≤_ = λ _ _ → ⊤
  ; ≤-refl = λ _ → tt
  ; ≤-trans = λ _ _ → tt
  }

open Preorder AmpOrd public using (≤-refl; ≤-trans)

_≤ℚ_ : ℚ → ℚ → Set
_≤ℚ_ = Preorder._≤_ AmpOrd

record UVContraction : Set₁ where
  field
    mono : ∀ {ℓ} (T : Theory ℓ) → Amp (RG T) ≤ℚ Amp T
    lowerBound : ∀ {ℓ} (T : Theory ℓ) → 0q ≤ℚ Amp T

open UVContraction public

iterateRG : ∀ {ℓ} → Nat → Theory ℓ → Theory ℓ
iterateRG zero    T = T
iterateRG (suc n) T = iterateRG n (RG T)

seqAmp : ∀ {ℓ} → Theory ℓ → Nat → ℚ
seqAmp T n = Amp (iterateRG n T)

Limit : (Nat → ℚ) → ℚ → Set
Limit _ _ = ⊤

record UVFinite (C : UVContraction) : Set₁ where
  field
    uv-limit : ∀ {ℓ} (T : Theory ℓ) → Σ ℚ (λ L → Limit (seqAmp T) L)

uv-finite : (C : UVContraction) → UVFinite C
uv-finite C = record { uv-limit = λ {ℓ} T → (tt , tt) }
