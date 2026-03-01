module DASHI.Geometry.LCP.CompleteInstance where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Geometry.LCP.Cauchy using (CauchyMod)
open import DASHI.Geometry.LCP.Limit using (limit; converges≥; lcp≥-mono)

-- Predicate-based ultrametric/completeness record.
record CompleteUltrametricBall {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  field
    Ball : ℕ → X → X → Set ℓ
    ball-refl : ∀ k x → Ball k x x
    ball-sym  : ∀ k x y → Ball k x y → Ball k y x
    ball-trans : ∀ k x y z → Ball k x y → Ball k y z → Ball k x z
    ball-mono : ∀ {j k} → j ≤ k → ∀ x y → Ball k x y → Ball j x y

    Cauchy : (ℕ → X) → Set ℓ
    lim : ∀ xs → Cauchy xs → X
    conv : ∀ xs (c : Cauchy xs) → ∀ k → Σ ℕ (λ N → ∀ {n} → N ≤ n → Ball k (xs n) (lim xs c))

open CompleteUltrametricBall public

ballLCP : ∀ {ℓ} {A : Set ℓ} → ℕ → Stream A → Stream A → Set ℓ
ballLCP k x y = lcp≥ x y k

Ball-refl : ∀ {ℓ} {A : Set ℓ} → ∀ k (x : Stream A) → ballLCP k x x
Ball-refl k x i i<k = refl

Ball-sym : ∀ {ℓ} {A : Set ℓ} → ∀ k (x y : Stream A) → ballLCP k x y → ballLCP k y x
Ball-sym k x y xy i i<k = sym (xy i i<k)
  where open import Relation.Binary.PropositionalEquality using (sym)

Ball-trans : ∀ {ℓ} {A : Set ℓ} → ∀ k (x y z : Stream A) → ballLCP k x y → ballLCP k y z → ballLCP k x z
Ball-trans k x y z xy yz i i<k = trans (xy i i<k) (yz i i<k)
  where open import Relation.Binary.PropositionalEquality using (trans)

Ball-mono : ∀ {ℓ} {A : Set ℓ} → ∀ {j k} → j ≤ k → ∀ (x y : Stream A) → ballLCP k x y → ballLCP j x y
Ball-mono j≤k x y hyp = lcp≥-mono j≤k hyp

completeLCP : ∀ {ℓ} {A : Set ℓ} → CompleteUltrametricBall (Stream A)
completeLCP {A = A} = record
  { Ball = ballLCP
  ; ball-refl = Ball-refl
  ; ball-sym = Ball-sym
  ; ball-trans = Ball-trans
  ; ball-mono = Ball-mono
  ; Cauchy = CauchyMod
  ; lim = limit
  ; conv = converges≥
  }
