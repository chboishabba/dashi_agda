module DASHI.Quantum.Unitary where

open import DASHI.Prelude
open import DASHI.OperatorTypes

-- Abstract “Hilbert-like” structure: we only need an inner product interface.
postulate
  ℂ : Set
  _≡ℂ_ : ℂ → ℂ → Set

record InnerProductSpace (S : Set) : Set₁ where
  field
    ⟪_,_⟫ : S → S → ℂ

-- Unitary = invertible + inner product preservation.
record Unitary {S : Set} (IPS : InnerProductSpace S) (U : S → S) : Set₁ where
  field
    inv : Invertible U
    preserves : ∀ x y → InnerProductSpace.⟪_,_⟫ IPS (U x) (U y) ≡ℂ InnerProductSpace.⟪_,_⟫ IPS x y
