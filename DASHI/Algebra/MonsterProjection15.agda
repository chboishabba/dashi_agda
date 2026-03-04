module DASHI.Algebra.MonsterProjection15 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Properties using (_≟_)

open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using
  (≤-refl; ≤-antisym; m∸n≡0⇒m≤n; n≢0⇒n>0; suc-injective; 1+n≢0)
open import Data.Vec using (Vec; []; _∷_)

open import DASHI.Algebra.MonsterMask15 using (Mask15; Kernel; projectTo)
open import DASHI.Algebra.MonsterUltrametric15 using (UMask15; dMask; lcpLen; len; id-zeroMask)
open import Ultrametric

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

lcpLen-zero→eq :
  ∀ {n} (x y : Vec Bool n) → lcpLen x y ≡ len x → x ≡ y
lcpLen-zero→eq [] [] _ = refl
lcpLen-zero→eq (true ∷ xs) (true ∷ ys) eq =
  cong (λ t → true ∷ t) (lcpLen-zero→eq xs ys (suc-injective eq))
lcpLen-zero→eq (false ∷ xs) (false ∷ ys) eq =
  cong (λ t → false ∷ t) (lcpLen-zero→eq xs ys (suc-injective eq))
lcpLen-zero→eq (true ∷ xs) (false ∷ ys) eq =
  ⊥-elim (1+n≢0 (sym eq))
lcpLen-zero→eq (false ∷ xs) (true ∷ ys) eq =
  ⊥-elim (1+n≢0 (sym eq))

lcpLen≤len : ∀ {n} (x y : Vec Bool n) → lcpLen x y ≤ len x
lcpLen≤len [] [] = z≤n
lcpLen≤len (true ∷ xs) (true ∷ ys) = s≤s (lcpLen≤len xs ys)
lcpLen≤len (false ∷ xs) (false ∷ ys) = s≤s (lcpLen≤len xs ys)
lcpLen≤len (true ∷ xs) (false ∷ ys) = z≤n
lcpLen≤len (false ∷ xs) (true ∷ ys) = z≤n

d0→eq : ∀ (x y : Mask15) → dMask x y ≡ 0 → x ≡ y
d0→eq x y eq =
  let
    len≤lcp : len x ≤ lcpLen x y
    len≤lcp = m∸n≡0⇒m≤n eq
    lcp≤len : lcpLen x y ≤ len x
    lcp≤len = lcpLen≤len x y
    lcp≡len : lcpLen x y ≡ len x
    lcp≡len = ≤-antisym lcp≤len len≤lcp
  in
  lcpLen-zero→eq x y lcp≡len

-- Contractive-on-distinct for projection:
-- d(Kx,Ky)=0 < d(x,y) because x≢y => d(x,y)≢0.
--
-- We’ll package it in your style.

record Contractive≢ (K : Mask15 → Mask15) : Set where
  open Ultrametric.Ultrametric UMask15
  field
    contraction≢ : ∀ {x y} → x ≢ y → d (K x) (K y) < d x y

-- For K = projectTo target, d(Kx,Ky)=0 always.
projContractive :
  ∀ target → Contractive≢ (Kernel.K (projectTo target))
projContractive target =
  record
    { contraction≢ = λ {x} {y} x≢y →
        let
          d0 : dMask target target ≡ 0
          d0 = id-zeroMask target
          dxy≢0 : dMask x y ≢ 0
          dxy≢0 eq = x≢y (d0→eq x y eq)
          dxy>0 = n≢0⇒n>0 dxy≢0
        in
        subst (λ t → t < dMask x y) (sym d0) dxy>0
    }
