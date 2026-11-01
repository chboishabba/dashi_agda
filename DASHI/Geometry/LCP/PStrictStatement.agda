module DASHI.Geometry.LCP.PStrictStatement where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Geometry.LCP.ContractiveCompose using (Strictκ)

-- Concrete, guard-based strictness statement template for P.
--
-- “FirstDiffAt x y k” says: x and y agree on the first k digits,
-- but disagree at digit k. This is the natural guard for
-- “projection kills the first difference”.
FirstDiffAt :
  ∀ {ℓ} {A : Set ℓ} →
  Stream A → Stream A → ℕ → Set ℓ
FirstDiffAt x y k =
  lcp≥ x y k × (x k ≢ y k)
  where
    infix 4 _≢_
    _≢_ : {ℓx : Level} {X : Set ℓx} → X → X → Set ℓx
    a ≢ b = ¬ (a ≡ b)

-- Guarded strictness: whenever the first difference is at k,
-- P pushes agreement by at least κ (often κ = 1 for tail-kill).
P-strict-on-first-diff :
  ∀ {ℓ} {A : Set ℓ} →
  (κ : ℕ) →
  (P : Stream A → Stream A) →
  Set ℓ
P-strict-on-first-diff κ P =
  ∀ x y k → FirstDiffAt x y k → lcp≥ (P x) (P y) (k + κ)

-- If you prefer a generic guard predicate (e.g. “NotSnap”),
-- use this wrapper instead.
P-strict-on-guard :
  ∀ {ℓ} {A : Set ℓ} →
  (κ : ℕ) →
  (P : Stream A → Stream A) →
  (Guard : Stream A → Stream A → Set ℓ) →
  Set ℓ
P-strict-on-guard κ P Guard =
  ∀ x y k → Guard x y → lcp≥ x y k → lcp≥ (P x) (P y) (k + κ)

-- From a guard-based statement, you can derive the Strictκ witness.
Strictκ-from-guard :
  ∀ {ℓ} {A : Set ℓ} →
  (κ : ℕ) →
  (P : Stream A → Stream A) →
  (Guard : Stream A → Stream A → Set ℓ) →
  P-strict-on-guard κ P Guard →
  (∀ x y → Guard x y) →
  Strictκ κ P
Strictκ-from-guard κ P Guard guardStrict guardAll x y k hyp =
  guardStrict x y k (guardAll x y) hyp
