module DASHI.Geometry.LCP.ContractiveCompose where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties as ℕₚ

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Geometry.LCP.Limit using (lcp≥-mono)

Nonexpansive :
  ∀ {ℓ} {A : Set ℓ}
  → (F : Stream A → Stream A)
  → Set ℓ
Nonexpansive F = ∀ x y k → lcp≥ x y k → lcp≥ (F x) (F y) k

Strictκ :
  ∀ {ℓ} {A : Set ℓ}
  → (κ : ℕ)
  → (F : Stream A → Stream A)
  → Set ℓ
Strictκ κ F = ∀ x y k → lcp≥ x y k → lcp≥ (F x) (F y) (k + κ)

Contractiveκ = Strictκ

Strict→Nonexp :
  ∀ {ℓ} {A : Set ℓ}
  → (κ : ℕ)
  → (F : Stream A → Stream A)
  → Strictκ κ F
  → Nonexpansive F
Strict→Nonexp κ F strict x y k hyp =
  lcp≥-mono (ℕₚ.m≤m+n k κ) (strict x y k hyp)

Nonexp-∘ :
  ∀ {ℓ} {A : Set ℓ}
  → (G F : Stream A → Stream A)
  → Nonexpansive G
  → Nonexpansive F
  → Nonexpansive (λ x → G (F x))
Nonexp-∘ G F Gne Fne x y k hyp =
  Gne (F x) (F y) k (Fne x y k hyp)

Strict∘Nonexp :
  ∀ {ℓ} {A : Set ℓ}
  → (κ : ℕ)
  → (G F : Stream A → Stream A)
  → Strictκ κ G
  → Nonexpansive F
  → Strictκ κ (λ x → G (F x))
Strict∘Nonexp κ G F Gstrict Fne x y k hyp =
  Gstrict (F x) (F y) k (Fne x y k hyp)

Nonexp∘Strict :
  ∀ {ℓ} {A : Set ℓ}
  → (κ : ℕ)
  → (G F : Stream A → Stream A)
  → Nonexpansive G
  → Strictκ κ F
  → Strictκ κ (λ x → G (F x))
Nonexp∘Strict κ G F Gne Fstrict x y k hyp =
  Gne (F x) (F y) (k + κ) (Fstrict x y k hyp)

Nonexp∘Strict∘Nonexp :
  ∀ {ℓ} {A : Set ℓ}
  → (κ : ℕ)
  → (C P R : Stream A → Stream A)
  → Nonexpansive C
  → Strictκ κ P
  → Nonexpansive R
  → Strictκ κ (λ x → C (P (R x)))
Nonexp∘Strict∘Nonexp κ C P R Cne Pstrict Rne =
  let PR-strict : Strictκ κ (λ x → P (R x))
      PR-strict = Strict∘Nonexp κ P R Pstrict Rne
  in
  Nonexp∘Strict κ C (λ x → P (R x)) Cne PR-strict
