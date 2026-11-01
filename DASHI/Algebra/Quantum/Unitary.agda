module DASHI.Algebra.Quantum.Unitary where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes

record ComplexAxioms : Set₁ where
  field
    ℂ : Set
    _≡ℂ_ : ℂ → ℂ → Set

open ComplexAxioms public

-- Abstract “Hilbert-like” structure: we only need an inner product interface.
record InnerProductSpace (A : ComplexAxioms) (S : Set) : Set₁ where
  field
    ⟪_,_⟫ : S → S → ℂ A

-- Unitary = invertible + inner product preservation.
record Unitary {A : ComplexAxioms} {S : Set} (IPS : InnerProductSpace A S) (U : S → S) : Set₁ where
  field
    inv : Invertible U
    preserves :
      ∀ x y →
        ComplexAxioms._≡ℂ_ A
          (InnerProductSpace.⟪_,_⟫ IPS (U x) (U y))
          (InnerProductSpace.⟪_,_⟫ IPS x y)
