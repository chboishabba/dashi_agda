module DASHI.Physics.ClosureKitLCP where

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)

open import DASHI.Geometry.LCP.Stream using (Stream)
open import DASHI.Geometry.LCP.FixedPointFromTContract as FP
open import DASHI.Geometry.LCP.ContractiveCompose using (Nonexpansive; Strictκ)

-- A small “kit” that wires T-contract → fixed point for LCP streams.
record LCPFixedPointKit {ℓ} {A : Set ℓ} : Set (lsuc ℓ) where
  field
    R : Stream A → Stream A
    P : Stream A → Stream A
    C : Stream A → Stream A
    R-nonexp : Nonexpansive R
    C-nonexp : Nonexpansive C
    κ : ℕ
    P-strict : Strictκ κ P
    κ′ : ℕ
    κ≡ : κ ≡ suc κ′
    x₀ : Stream A

    fp : Stream A
    fixed : ∀ i → C (P (R fp)) i ≡ fp i
    unique : ∀ y → (∀ i → C (P (R y)) i ≡ y i) → (∀ i → y i ≡ fp i)

open LCPFixedPointKit public

buildLCPFixedPoint :
  ∀ {ℓ} {A : Set ℓ} →
  (R P C : Stream A → Stream A) →
  (R-nonexp : Nonexpansive R) →
  (C-nonexp : Nonexpansive C) →
  (κ : ℕ) →
  (P-strict : Strictκ κ P) →
  (κ′ : ℕ) →
  (κ≡ : κ ≡ suc κ′) →
  (x₀ : Stream A) →
  LCPFixedPointKit {A = A}
buildLCPFixedPoint {A = A} R P C R-nonexp C-nonexp κ P-strict κ′ κ≡ x₀ =
  let
    res = FP.fixedPointFromTContract {A = A} R P C R-nonexp C-nonexp κ P-strict κ′ κ≡ x₀
  in
  record
    { R = R
    ; P = P
    ; C = C
    ; R-nonexp = R-nonexp
    ; C-nonexp = C-nonexp
    ; κ = κ
    ; P-strict = P-strict
    ; κ′ = κ′
    ; κ≡ = κ≡
    ; x₀ = x₀
    ; fp = proj₁ res
    ; fixed = proj₁ (proj₂ res)
    ; unique = proj₂ (proj₂ res)
    }
