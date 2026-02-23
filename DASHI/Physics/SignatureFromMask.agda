module DASHI.Physics.SignatureFromMask where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.IndefiniteMaskQuadratic using (Sign; plus; minus)

------------------------------------------------------------------------
-- Count plus/minus in a mask and extract signature

countPlus : ∀ {m : Nat} → Vec Sign m → Nat
countPlus [] = 0
countPlus (plus  ∷ σ) = suc (countPlus σ)
countPlus (minus ∷ σ) = countPlus σ

countMinus : ∀ {m : Nat} → Vec Sign m → Nat
countMinus [] = 0
countMinus (plus  ∷ σ) = countMinus σ
countMinus (minus ∷ σ) = suc (countMinus σ)

signature : ∀ {m : Nat} → Vec Sign m → Nat × Nat
signature σ = (countMinus σ , countPlus σ)

------------------------------------------------------------------------
-- A concrete mask constructor: one minus, rest plus

replicatePlus : ∀ (k : Nat) → Vec Sign k
replicatePlus zero    = []
replicatePlus (suc k) = plus ∷ replicatePlus k

oneMinusRestPlus : ∀ {m : Nat} → Vec Sign (suc m)
oneMinusRestPlus {m} = minus ∷ replicatePlus m

------------------------------------------------------------------------
-- Signature of the concrete mask

countPlus-replicatePlus :
  ∀ {m : Nat} → countPlus (replicatePlus m) ≡ m
countPlus-replicatePlus {zero} = refl
countPlus-replicatePlus {suc m} =
  cong suc (countPlus-replicatePlus {m})

countMinus-replicatePlus :
  ∀ {m : Nat} → countMinus (replicatePlus m) ≡ 0
countMinus-replicatePlus {zero} = refl
countMinus-replicatePlus {suc m} = countMinus-replicatePlus {m}

signature-oneMinus :
  ∀ {m : Nat} → signature (oneMinusRestPlus {m}) ≡ (suc 0 , m)
signature-oneMinus {m} =
  cong₂ _,_
    (cong suc (countMinus-replicatePlus {m}))
    (countPlus-replicatePlus {m})
