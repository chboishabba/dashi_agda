module DASHI.Geometry.LCP.Banach where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; pred)
open import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Data.Sum using (inj₁; inj₂)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Geometry.LCP.Cauchy using (CauchyMod)
open import DASHI.Geometry.LCP.Limit using (limit; converges≥; lcp≥-mono; lcp≥-at)
open import DASHI.Geometry.LCP.NatGlue using (mul-κ-lower)

-- κ-contractivity in depth form: agreement on k ⇒ agreement on k+κ.
Contractiveκ : ∀ {ℓ} {A : Set ℓ} → ℕ → (Stream A → Stream A) → Set ℓ
Contractiveκ κ T = ∀ x y k → lcp≥ x y k → lcp≥ (T x) (T y) (k + κ)

iter : ∀ {ℓ} {A : Set ℓ} → (Stream A → Stream A) → Stream A → ℕ → Stream A
iter T x₀ zero    = x₀
iter T x₀ (suc n) = T (iter T x₀ n)

-- Orbit step depth growth.
-- Multiplication recurses on the left, so this is definitional.
suc-mul-left : ∀ (n κ : ℕ) → suc n * κ ≡ κ + n * κ
suc-mul-left n κ = refl

orbit-step :
  ∀ {ℓ} {A : Set ℓ}
  → (κ : ℕ) → (T : Stream A → Stream A) → Contractiveκ κ T
  → (x₀ : Stream A)
  → ∀ n → lcp≥ (iter T x₀ n) (iter T x₀ (suc n)) (n * κ)
orbit-step κ T ctr x₀ zero =
  λ i ()
orbit-step κ T ctr x₀ (suc n) =
  let
    step : lcp≥ (iter T x₀ (suc n)) (iter T x₀ (suc (suc n))) (n * κ + κ)
    step = ctr (iter T x₀ n) (iter T x₀ (suc n)) (n * κ)
               (orbit-step κ T ctr x₀ n)
    step' : lcp≥ (iter T x₀ (suc n)) (iter T x₀ (suc (suc n))) (κ + n * κ)
    step' = subst
      (λ k → lcp≥ (iter T x₀ (suc n)) (iter T x₀ (suc (suc n))) k)
      (NatP.+-comm (n * κ) κ) step
  in
  -- rewrite (suc n * κ) as (n * κ + κ)
  subst (λ k → lcp≥ (iter T x₀ (suc n)) (iter T x₀ (suc (suc n))) k)
        (sym (suc-mul-left n κ)) step'

-- Chain agreement across an interval using transitivity.
chain-lcp≥ :
  ∀ {ℓ} {A : Set ℓ}
  → (xs : ℕ → Stream A)
  → (k : ℕ)
  → ∀ {m n} → m ≤ n
  → (∀ t → m ≤ t → t < n → lcp≥ (xs t) (xs (suc t)) k)
  → lcp≥ (xs m) (xs n) k
chain-lcp≥ xs k {m} {n} m≤n adj =
  go n m≤n adj
  where
    go : ∀ n → m ≤ n
       → (∀ t → m ≤ t → t < n → lcp≥ (xs t) (xs (suc t)) k)
       → lcp≥ (xs m) (xs n) k
    go zero m≤0 adj' =
      let
        m≡0 : m ≡ 0
        m≡0 = NatP.n≤0⇒n≡0 m≤0
      in
      subst (λ t → lcp≥ (xs t) (xs zero) k) (sym m≡0) (λ i i<k → refl)
    go (suc n') m≤sn adj' with NatP.m≤n⇒m<n∨m≡n m≤sn
    ... | inj₂ m≡sn =
      λ i i<k → subst (λ t → xs m i ≡ xs t i) m≡sn refl
    ... | inj₁ m<sn =
      let
        m≤n' : m ≤ n'
        m≤n' = NatP.≤-pred m<sn
        ih : lcp≥ (xs m) (xs n') k
        ih = go n' m≤n'
               (λ t m≤t t<n' → adj' t m≤t (NatP.<-trans t<n' (NatP.n<1+n n')))
        step : lcp≥ (xs n') (xs (suc n')) k
        step = adj' n' m≤n' (NatP.n<1+n n')
      in
      λ i i<k → trans (ih i i<k) (step i i<k)

-- Orbit is Cauchy (monotone modulus: N k = k)
orbit-cauchy :
  ∀ {ℓ} {A : Set ℓ}
  → (κ′ : ℕ) → (T : Stream A → Stream A) → Contractiveκ (suc κ′) T
  → (x₀ : Stream A)
  → CauchyMod (iter T x₀)
orbit-cauchy κ′ T ctr x₀ =
  record
    { N = λ k → k
    ; mono = λ k j k≤j → k≤j
    ; mod = mod'
    }
  where
    mod' : ∀ k {m n} → k ≤ m → k ≤ n → lcp≥ (iter T x₀ m) (iter T x₀ n) k
    mod' k {m} {n} k≤m k≤n with NatP.≤-total m n
    ... | inj₁ m≤n =
      chain-lcp≥ (iter T x₀) k m≤n
        (λ t m≤t t<n →
           lcp≥-mono (mul-κ-lower κ′ (NatP.≤-trans k≤m m≤t))
             (orbit-step (suc κ′) T ctr x₀ t))
    ... | inj₂ n≤m =
      λ i i<k →
        sym (chain-lcp≥ (iter T x₀) k n≤m
              (λ t n≤t t<m →
                 lcp≥-mono (mul-κ-lower κ′ (NatP.≤-trans k≤n n≤t))
                   (orbit-step (suc κ′) T ctr x₀ t))
              i i<k)

x★ : ∀ {ℓ} {A : Set ℓ}
   → (κ′ : ℕ) → (T : Stream A → Stream A) → Contractiveκ (suc κ′) T
   → (x₀ : Stream A)
   → Stream A
x★ κ′ T ctr x₀ = limit (iter T x₀) (orbit-cauchy κ′ T ctr x₀)

postulate
  fixed :
    ∀ {ℓ} {A : Set ℓ}
    → (κ′ : ℕ) → (T : Stream A → Stream A) → (ctr : Contractiveκ (suc κ′) T)
    → (x₀ : Stream A)
    → (∀ i → T (x★ κ′ T ctr x₀) i ≡ x★ κ′ T ctr x₀ i)

  unique :
    ∀ {ℓ} {A : Set ℓ}
    → (κ′ : ℕ) → (T : Stream A → Stream A) → (ctr : Contractiveκ (suc κ′) T)
    → ∀ (u v : Stream A)
    → (∀ i → T u i ≡ u i)
    → (∀ i → T v i ≡ v i)
    → (∀ i → u i ≡ v i)

Banach-LCP :
  ∀ {ℓ} {A : Set ℓ}
  → (κ′ : ℕ) → (T : Stream A → Stream A) → Contractiveκ (suc κ′) T
  → (x₀ : Stream A)
  → Σ (Stream A) (λ x → (∀ i → T x i ≡ x i) × (∀ y → (∀ i → T y i ≡ y i) → (∀ i → y i ≡ x i)))
Banach-LCP κ′ T ctr x₀ =
  x★ κ′ T ctr x₀ ,
    ( fixed κ′ T ctr x₀
    , λ y yfix i → unique κ′ T ctr y (x★ κ′ T ctr x₀) yfix (fixed κ′ T ctr x₀) i
    )
