module DASHI.Geometry.LCP.FixedPointFromTContract where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Product using (Σ; _,_; _×_)

open import DASHI.Geometry.LCP.Stream using (Stream)
open import DASHI.Geometry.LCP.Banach as Banach
open import DASHI.Geometry.LCP.TContractiveDepth as TCD

module _ {ℓ} {A : Set ℓ} where

  -- Wire T-contract into Banach-LCP.
  -- We expose κ′ and a proof κ ≡ suc κ′ to keep it total.
  fixedPointFromTContract :
    (κ′ : ℕ) →
    TCD.κ {A = A} ≡ suc κ′ →
    (x₀ : Stream A) →
    Σ (Stream A) (λ x →
      (∀ i → TCD.T {A = A} x i ≡ x i)
      × (∀ y → (∀ i → TCD.T {A = A} y i ≡ y i) → (∀ i → y i ≡ x i)))
  fixedPointFromTContract κ′ κ≡ x₀ =
    Banach.Banach-LCP κ′ (TCD.T {A = A})
      (subst (λ k → Banach.Contractiveκ k (TCD.T {A = A})) κ≡ (TCD.T-contract {A = A}))
      x₀
