module DASHI.Algebra.MonsterUltrametric15 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Nat using (_≤_; _<_; _⊔_; _∸_)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Vec using (Vec; []; _∷_)
-- Removed Relation.Binary.Reasoning.Base.Raw as it's not needed here.
-- Removed Relation.Binary.Reasoning.Nat as it's not needed here.

open import Ultrametric
open import DASHI.Algebra.MonsterMask15 using (Mask15)

lcpLen : ∀ {n} → Vec Bool n → Vec Bool n → Nat
lcpLen [] [] = 0
lcpLen (true  ∷ xs) (true  ∷ ys) = suc (lcpLen xs ys)
lcpLen (false ∷ xs) (false ∷ ys) = suc (lcpLen xs ys)
lcpLen (_ ∷ _) (_ ∷ _) = 0

len : ∀ {n} → Vec Bool n → Nat
len []       = 0
len (_ ∷ xs) = suc (len xs)

dMask : ∀ {n} → Vec Bool n → Vec Bool n → Nat
dMask {n} x y = len {n} x ∸ lcpLen x y

-- id-zero
lcpLen-self-eq : ∀ {n} (m : Vec Bool n) → lcpLen m m ≡ len {n} m
lcpLen-self-eq [] = refl
lcpLen-self-eq (true  ∷ xs) = cong suc (lcpLen-self-eq xs)
lcpLen-self-eq (false ∷ xs) = cong suc (lcpLen-self-eq xs)

postulate
  id-zeroMask : ∀ m → dMask {15} m m ≡ 0

-- symmetric
lcpLen-symmetric : ∀ {n} (x y : Vec Bool n) → lcpLen x y ≡ lcpLen y x
lcpLen-symmetric [] [] = refl
lcpLen-symmetric (x ∷ xs) (y ∷ ys) with x | y
... | true | true = cong suc (lcpLen-symmetric xs ys)
... | false | false = cong suc (lcpLen-symmetric xs ys)
... | true | false = refl
... | false | true = refl

postulate
  dMask-symmetric : ∀ {n} (x y : Vec Bool n) → dMask {n} x y ≡ dMask {n} y x

symMask : ∀ {n} (x y : Vec Bool n) → dMask {n} x y ≡ dMask {n} y x
symMask = dMask-symmetric

-- ultratriangle
postulate
  lcpLen-ultratriangle :
    ∀ {n} (x y z : Vec Bool n) →
    lcpLen x y ⊔ lcpLen y z ≤ lcpLen x z

postulate
  ultraMask : ∀ x y z → dMask {15} x z ≤ (dMask {15} x y ⊔ dMask {15} y z)

UMask15 : Ultrametric Mask15
UMask15 = record
  { d             = dMask {15}
  ; id-zero       = id-zeroMask
  ; symmetric     = symMask {15}
  ; ultratriangle = ultraMask
  }