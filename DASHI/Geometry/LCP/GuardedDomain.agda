module DASHI.Geometry.LCP.GuardedDomain where

open import Agda.Primitive using (Level; _⊔_)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Geometry.LCP.Banach using (Contractiveκ; Banach-LCP)

-- Guarded domain wrapper: Xg = Σ x, Guard x.
Guarded :
  ∀ {ℓ} {A : Set ℓ} →
  (Guard : Stream A → Set ℓ) →
  Set (ℓ ⊔ ℓ)
Guarded {A = A} Guard = Σ (Stream A) Guard

-- Lift lcp≥ to the guarded domain (ignore the proof component).
glcp≥ :
  ∀ {ℓ} {A : Set ℓ} {Guard : Stream A → Set ℓ} →
  Guarded Guard → Guarded Guard → ℕ → Set ℓ
glcp≥ {Guard = Guard} x y k = lcp≥ (proj₁ x) (proj₁ y) k

-- A guarded map: T with closure over Guard.
record GuardedMap {ℓ} {A : Set ℓ} (Guard : Stream A → Set ℓ) : Set (ℓ ⊔ ℓ) where
  field
    T : Stream A → Stream A
    closed : ∀ x → Guard x → Guard (T x)

open GuardedMap public

-- Lift T to the guarded domain.
Tg :
  ∀ {ℓ} {A : Set ℓ} {Guard : Stream A → Set ℓ} →
  GuardedMap Guard → Guarded Guard → Guarded Guard
Tg {Guard = Guard} g x =
  (T g (proj₁ x)) , closed g (proj₁ x) (proj₂ x)

-- Guarded contractivity: contractive on the Guarded domain.
GuardedContractiveκ :
  ∀ {ℓ} {A : Set ℓ} {Guard : Stream A → Set ℓ} →
  (κ : ℕ) →
  GuardedMap Guard →
  Set (ℓ ⊔ ℓ)
GuardedContractiveκ κ g =
  ∀ x y k →
    glcp≥ x y k →
    glcp≥ (Tg g x) (Tg g y) (k + κ)

-- If you can show base contractivity under Guard, you get guarded contractivity.
lift-guarded :
  ∀ {ℓ} {A : Set ℓ} {Guard : Stream A → Set ℓ} →
  (κ : ℕ) →
  (g : GuardedMap Guard) →
  (∀ x y k → Guard x → Guard y → lcp≥ x y k → lcp≥ (T g x) (T g y) (k + κ)) →
  GuardedContractiveκ κ g
lift-guarded κ g ctr x y k hyp =
  ctr (proj₁ x) (proj₁ y) k (proj₂ x) (proj₂ y) hyp

-- If you want a Banach fixed-point result on Guarded, use FixedPointFromTContract
-- on a concrete guarded instance and then lift via the Guard proof.
