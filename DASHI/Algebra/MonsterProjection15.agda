module DASHI.Algebra.MonsterProjection15 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Data.Bool.Properties using (_≟_)

open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Vec using (Vec; []; _∷_)

open import DASHI.Algebra.MonsterMask15 using (Mask15; Kernel; projectTo)
open import DASHI.Algebra.MonsterUltrametric15 using (UMask15; dMask; lcpLen; len)
open import Ultrametric

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

postulate
  lcpLen-zero→eq :
    ∀ {n} (x y : Vec Bool n) → lcpLen x y ≡ len x → x ≡ y

postulate
  d0→eq : ∀ (x y : Mask15) → dMask x y ≡ 0 → x ≡ y

-- Contractive-on-distinct for projection:
-- d(Kx,Ky)=0 < d(x,y) because x≢y => d(x,y)≢0.
--
-- We’ll package it in your style.

record Contractive≢ (K : Mask15 → Mask15) : Set where
  open Ultrametric.Ultrametric UMask15
  field
    contraction≢ : ∀ {x y} → x ≢ y → d (K x) (K y) < d x y

-- For K = projectTo target, d(Kx,Ky)=0 always.
postulate
  projContractive :
    ∀ target → Contractive≢ (Kernel.K (projectTo target))
