module DASHI.Physics.RealTernaryCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import DASHI.Algebra.Trit using (Trit; inv; inv-invol; zer)

Carrier : Nat → Set
Carrier n = Vec Trit n

invVec : ∀ {n} → Carrier n → Carrier n
invVec {n} = map inv

invVec-invol : ∀ {n} (x : Carrier n) → invVec (invVec x) ≡ x
invVec-invol [] = refl
invVec-invol (t ∷ ts) rewrite inv-invol t | invVec-invol ts = refl

zeroVec : ∀ {n} → Carrier n
zeroVec {n = zero} = []
zeroVec {n = suc n} = zer ∷ zeroVec {n}
