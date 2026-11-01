module DASHI.Geometry.LCP.Limit where

open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
open import Data.Nat.Properties as NatP

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Geometry.LCP.Cauchy using (CauchyMod; N; mono; mod)

Nof : ∀ {ℓ} {A : Set ℓ} → (xs : ℕ → Stream A) → CauchyMod xs → ℕ → ℕ
Nof xs c k = N c k

limit : ∀ {ℓ} {A : Set ℓ} → (xs : ℕ → Stream A) → CauchyMod xs → Stream A
limit xs c i = (xs (Nof xs c (suc i))) i

-- Helper lemmas (postulates removed).
lcp≥-mono :
  ∀ {ℓ} {A : Set ℓ} {x y : Stream A} {j k}
  → j ≤ k → lcp≥ x y k → lcp≥ x y j
lcp≥-mono j≤k hyp i i<j = hyp i (NatP.<-≤-trans i<j j≤k)

lcp≥-at :
  ∀ {ℓ} {A : Set ℓ} {x y : Stream A}
  → ∀ i → lcp≥ x y (suc i) → x i ≡ y i
lcp≥-at i hyp = hyp i (NatP.n<1+n i)

-- Convergence: eventually xs n agrees with limit on first k digits.
converges≥ :
  ∀ {ℓ} {A : Set ℓ}
  → (xs : ℕ → Stream A)
  → (c : CauchyMod xs)
  → ∀ k → Σ ℕ (λ N → ∀ {n} → N ≤ n → lcp≥ (xs n) (limit xs c) k)
converges≥ {A = A} xs c k =
  let Nk = Nof xs c (suc k)
      wk = mod c (suc k)
  in
  Nk , λ {n} n≥Nk i i<k →
        let
          Nk' = Nof xs c (suc i)
          wk' = mod c (suc i)
          Nk'≤Nk = mono c (suc i) (suc k) (s≤s (NatP.<⇒≤ i<k))
          Nk'≤n = NatP.≤-trans Nk'≤Nk n≥Nk
        in
        let
          wkn = wk' {m = Nk'} {n = n} NatP.≤-refl Nk'≤n
        in
        sym (lcp≥-at {x = xs Nk'} {y = xs n} i wkn)
