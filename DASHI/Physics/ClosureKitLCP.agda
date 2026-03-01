module DASHI.Physics.ClosureKitLCP where

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)

open import DASHI.Geometry.LCP.Stream using (Stream)
open import DASHI.Geometry.LCP.FixedPointFromTContract as FP
open import DASHI.Geometry.LCP.TContractiveDepth as TCD

-- A small “kit” that wires T-contract → fixed point for LCP streams.
record LCPFixedPointKit {ℓ} {A : Set ℓ} : Set (lsuc ℓ) where
  field
    κ′ : ℕ
    κ≡ : TCD.κ {A = A} ≡ suc κ′
    x₀ : Stream A

    fp : Stream A
    fixed : ∀ i → TCD.T {A = A} fp i ≡ fp i
    unique : ∀ y → (∀ i → TCD.T {A = A} y i ≡ y i) → (∀ i → y i ≡ fp i)

open LCPFixedPointKit public

buildLCPFixedPoint :
  ∀ {ℓ} {A : Set ℓ} →
  (κ′ : ℕ) →
  (κ≡ : TCD.κ {A = A} ≡ suc κ′) →
  (x₀ : Stream A) →
  LCPFixedPointKit {A = A}
buildLCPFixedPoint {A = A} κ′ κ≡ x₀ =
  let
    res = FP.fixedPointFromTContract {A = A} κ′ κ≡ x₀
  in
  record
    { κ′ = κ′
    ; κ≡ = κ≡
    ; x₀ = x₀
    ; fp = proj₁ res
    ; fixed = proj₁ (proj₂ res)
    ; unique = proj₂ (proj₂ res)
    }
