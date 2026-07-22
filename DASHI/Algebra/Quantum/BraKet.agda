module DASHI.Algebra.Quantum.BraKet where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.Quantum.Unitary

------------------------------------------------------------------------
-- Explicit notation-level wrappers around the existing abstract inner product.
-- This adds no new Hilbert-space authority: bras are the canonical wrappers of
-- vectors supplied by the same inner-product carrier.

record Ket (S : Set) : Set where
  constructor ket
  field
    ketVector : S

open Ket public

record Bra (S : Set) : Set where
  constructor bra
  field
    braVector : S

open Bra public

braOf : ∀ {S} → Ket S → Bra S
braOf (ket ψ) = bra ψ

ketOf : ∀ {S} → Bra S → Ket S
ketOf (bra ψ) = ket ψ

braOf-ketOf :
  ∀ {S} (φ : Bra S) →
  braOf (ketOf φ) ≡ φ
braOf-ketOf (bra _) = refl

ketOf-braOf :
  ∀ {S} (ψ : Ket S) →
  ketOf (braOf ψ) ≡ ψ
ketOf-braOf (ket _) = refl

braKet :
  ∀ {A : ComplexAxioms} {S : Set} →
  InnerProductSpace A S →
  Bra S →
  Ket S →
  ComplexAxioms.ℂ A
braKet IPS (bra φ) (ket ψ) =
  InnerProductSpace.⟪_,_⟫ IPS φ ψ

ketBraDiagonal :
  ∀ {A : ComplexAxioms} {S : Set} →
  (IPS : InnerProductSpace A S) →
  (ψ : Ket S) →
  braKet IPS (braOf ψ) ψ
  ≡ InnerProductSpace.⟪_,_⟫ IPS (ketVector ψ) (ketVector ψ)
ketBraDiagonal IPS (ket ψ) = refl

record BraKetInterface
  (A : ComplexAxioms)
  (S : Set)
  (IPS : InnerProductSpace A S) : Set₁ where
  field
    makeKet : S → Ket S
    makeBra : Ket S → Bra S
    bracket : Bra S → Ket S → ComplexAxioms.ℂ A
    bracketIsInnerProduct :
      ∀ φ ψ →
      bracket (makeBra (makeKet φ)) (makeKet ψ)
      ≡ InnerProductSpace.⟪_,_⟫ IPS φ ψ

open BraKetInterface public

canonicalBraKetInterface :
  ∀ {A : ComplexAxioms} {S : Set} →
  (IPS : InnerProductSpace A S) →
  BraKetInterface A S IPS
canonicalBraKetInterface IPS =
  record
    { makeKet = ket
    ; makeBra = braOf
    ; bracket = braKet IPS
    ; bracketIsInnerProduct = λ _ _ → refl
    }
