module DASHI.Algebra.MonsterMask15 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

FactorCount : Nat
FactorCount = 15

Mask15 : Set
Mask15 = Vec Bool FactorCount

fullMask : Mask15
fullMask = replicate FactorCount true

emptyMask : Mask15
emptyMask = replicate FactorCount false

-- Pointwise AND (same length, total)
boolAnd : Bool → Bool → Bool
boolAnd true true = true
boolAnd _    _    = false

_∧_ : ∀ {n} → Vec Bool n → Vec Bool n → Vec Bool n
_∧_ {zero} [] [] = []
_∧_ {suc n} (b ∷ xs) (c ∷ ys) = boolAnd b c ∷ (xs ∧ ys)

-- Kernel interface (15-fixed)
record Kernel : Set₁ where
  field
    K : Mask15 → Mask15

projectTo : Mask15 → Kernel
projectTo target = record { K = λ _ → target }
