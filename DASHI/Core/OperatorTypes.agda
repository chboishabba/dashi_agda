module DASHI.Core.OperatorTypes where

open import DASHI.Core.Prelude
open import DASHI.Core.KernelMonoid using (Kernel; KernelEq)

-- Invertible (bijection witness).
record Invertible {S : Set} (K : S → S) : Set where
  field
    inv   : S → S
    left  : ∀ x → inv (K x) ≡ x
    right : ∀ x → K (inv x) ≡ x

-- Projection = idempotent operator.
record Projection {S : Set} (K : S → S) : Set where
  field idem : ∀ x → K (K x) ≡ K x

-- (Optional) Nontrivial projection means not identity.
Nontrivial : ∀ {S} (K : S → S) → Set
Nontrivial {S} K = ¬ (∀ x → K x ≡ x)

-- Regular inverse (von Neumann regular): a = a*b*a in an algebraic carrier.
-- Here: “regularizer” for endofunctions, expressed as K = K ∘ R ∘ K.
record Regularizer {S : Set} (K : S → S) : Set where
  field
    R : S → S
    law : ∀ x → K x ≡ K (R (K x))

-- A simple operator “tag” classifier you can populate later.
data OpClass : Set where
  invertible projection regular other : OpClass

-- Classification is a *goal*: you can decide per operator, not assumed.
record Classifies {S : Set} (K : S → S) : Set₁ where
  field
    class : OpClass
    sound :
      (class ≡ invertible → Invertible K) ×
      (class ≡ projection  → Projection K) ×
      (class ≡ regular     → Regularizer K)
