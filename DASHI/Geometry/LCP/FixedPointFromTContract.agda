module DASHI.Geometry.LCP.FixedPointFromTContract where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Product using (Σ; _,_; _×_)

open import DASHI.Geometry.LCP.Stream using (Stream)
open import DASHI.Geometry.LCP.Banach as Banach
open import DASHI.Geometry.LCP.ContractiveCompose as CC using (Nonexp∘Strict∘Nonexp)
open import DASHI.Geometry.LCP.ContractiveCompose using (Nonexpansive; Strictκ)

module _ {ℓ} {A : Set ℓ} where

  -- Wire T-contract into Banach-LCP.
  -- We expose κ′ and a proof κ ≡ suc κ′ to keep it total.
  fixedPointFromTContract :
    (R P C : Stream A → Stream A) →
    (R-nonexp : Nonexpansive R) →
    (C-nonexp : Nonexpansive C) →
    (κ : ℕ) →
    (P-strict : Strictκ κ P) →
    (κ′ : ℕ) →
    κ ≡ suc κ′ →
    (x₀ : Stream A) →
    Σ (Stream A) (λ x →
      (∀ i → C (P (R x)) i ≡ x i)
      × (∀ y → (∀ i → C (P (R y)) i ≡ y i) → (∀ i → y i ≡ x i)))
  fixedPointFromTContract R P C R-nonexp C-nonexp κ P-strict κ′ κ≡ x₀ =
    let
      T : Stream A → Stream A
      T x = C (P (R x))

      T-contract : CC.Contractiveκ κ T
      T-contract = Nonexp∘Strict∘Nonexp κ C P R C-nonexp P-strict R-nonexp
    in
    Banach.Banach-LCP κ′ T
      (subst (λ k → Banach.Contractiveκ k T) κ≡ T-contract)
      x₀
