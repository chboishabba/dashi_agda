module DASHI.Physics.QuadraticCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import Data.Vec using (Vec; []; _∷_; _++_; map)
open import Data.Product using (proj₁; proj₂)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.CanonicalizationMinimal as CM

------------------------------------------------------------------------
-- Quadratic “energy” density per trit: squares of {-1,0,+1}
-- Encoded directly as Nat: 1 for ±, 0 for 0.

sqTrit : Trit → Nat
sqTrit neg = 1
sqTrit zer = 0
sqTrit pos = 1

sumNat : ∀ {m : Nat} → Vec Nat m → Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

------------------------------------------------------------------------
-- Quadratic invariant on the core: sum of squares

Qcore : ∀ {m : Nat} → Vec Trit m → Nat
Qcore c = sumNat (map sqTrit c)

------------------------------------------------------------------------
-- Canonicalization preserves squares pointwise

sq-canon : ∀ t → sqTrit (CM.canonTrit t) ≡ sqTrit t
sq-canon neg = refl
sq-canon zer = refl
sq-canon pos = refl

------------------------------------------------------------------------
-- Qcore invariance under canonVec

Qcore-canonVec : ∀ {m : Nat} (c : Vec Trit m) → Qcore (CM.canonVec c) ≡ Qcore c
Qcore-canonVec [] = refl
Qcore-canonVec (t ∷ ts)
  rewrite sq-canon t
  = cong (λ n → sqTrit t + n) (Qcore-canonVec ts)

------------------------------------------------------------------------
-- Lift Qcore to the full state via the coarse split

Qfull : ∀ {m k : Nat} → Vec Trit (m + k) → Nat
Qfull {m} {k} x = Qcore (TCP.coarseOf m k x)

Qfull-invariant-Cᵣ :
  ∀ {m k : Nat} (x : Vec Trit (m + k)) →
  Qfull {m} {k} (CM.Cᵣ {m} {k} x) ≡ Qfull {m} {k} x
Qfull-invariant-Cᵣ {m} {k} x with TCP.split m k x
... | p
  rewrite TCP.split-++ m k (CM.canonVec (proj₁ p)) (proj₂ p)
        | TCP.split-++ m k (proj₁ p) (proj₂ p)
  = Qcore-canonVec (proj₁ p)
