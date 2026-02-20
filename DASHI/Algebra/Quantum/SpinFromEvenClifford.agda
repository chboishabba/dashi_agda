
module DASHI.Algebra.Quantum.SpinFromEvenClifford where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

record SpinData : Set₁ where
  field
    SO : Nat → Nat → Set
    Cl⁰ : Set
    Spin : Set
    toSO : Spin → SO 3 1
    kernel±1 : Set
    identitySO : SO 3 1

record SpinDoubleCover (D : SpinData) : Set₁ where
  open SpinData D
  field
    hom : Spin → SO 3 1
    kernel : Spin → Set
    kernel⊆±1 : ∀ s → hom s ≡ identitySO → kernel s → kernel±1
    surjective : ∀ g → Σ Spin (λ s → hom s ≡ g)

-- Building a witness now requires surjectivity/kernel proof data.
spinDoubleCover-witness :
  ∀ D →
  (ker : SpinData.Spin D → Set)
  (ker⊆±1 : ∀ s → SpinData.toSO D s ≡ SpinData.identitySO D → ker s → SpinData.kernel±1 D)
  (surj : ∀ g → Σ (SpinData.Spin D) (λ s → SpinData.toSO D s ≡ g)) →
  SpinDoubleCover D
spinDoubleCover-witness D ker ker⊆±1 surj =
  record { hom = SpinData.toSO D ; kernel = ker ; kernel⊆±1 = ker⊆±1 ; surjective = surj }

SpinIsDoubleCover : ∀ {D} → SpinDoubleCover D → Set
SpinIsDoubleCover {D} cover =
  ∀ g → Σ (SpinData.Spin D) (λ s → SpinDoubleCover.hom cover s ≡ g)
