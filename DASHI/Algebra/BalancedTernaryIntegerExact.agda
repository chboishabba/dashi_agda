module DASHI.Algebra.BalancedTernaryIntegerExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer using (ℤ; +_) renaming (_-_ to _-ℤ_)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- Hunhold Definition 3, represented first as exact positive/negative weight
-- ledgers.  This avoids quotienting away cancellation before the signed-radix
-- structure has been exposed.

record SignedWeight : Set where
  constructor signedWeight
  field
    positiveWeight : Nat
    negativeWeight : Nat
open SignedWeight public

zeroWeight : SignedWeight
zeroWeight = signedWeight 0 0

tritWeight : Trit.Trit → SignedWeight
tritWeight Trit.neg = signedWeight 0 1
tritWeight Trit.zer = zeroWeight
tritWeight Trit.pos = signedWeight 1 0

addWeight : SignedWeight → SignedWeight → SignedWeight
addWeight (signedWeight p n) (signedWeight q m) =
  signedWeight (p + q) (n + m)

scaleThree : SignedWeight → SignedWeight
scaleThree (signedWeight p n) = signedWeight (3 * p) (3 * n)

swapSign : SignedWeight → SignedWeight
swapSign (signedWeight p n) = signedWeight n p

swapSign-involutive : (w : SignedWeight) → swapSign (swapSign w) ≡ w
swapSign-involutive (signedWeight p n) = refl

-- Least-significant trit is at the head:
-- eval (t0 ∷ t1 ∷ ...) = t0 + 3 t1 + 3^2 t2 + ...
eval : ∀ {n} → Vec Trit.Trit n → SignedWeight
eval [] = zeroWeight
eval (t ∷ ts) = addWeight (tritWeight t) (scaleThree (eval ts))

invertWord : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
invertWord [] = []
invertWord (t ∷ ts) = Trit.inv t ∷ invertWord ts

tritWeight-involution :
  (t : Trit.Trit) → tritWeight (Trit.inv t) ≡ swapSign (tritWeight t)
tritWeight-involution Trit.neg = refl
tritWeight-involution Trit.zer = refl
tritWeight-involution Trit.pos = refl

eval-involution :
  ∀ {n} (ts : Vec Trit.Trit n) →
  eval (invertWord ts) ≡ swapSign (eval ts)
eval-involution [] = refl
eval-involution (t ∷ ts)
  rewrite tritWeight-involution t
        | eval-involution ts = refl

toInteger : SignedWeight → ℤ
toInteger w =
  (+ (positiveWeight w)) -ℤ (+ (negativeWeight w))

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

------------------------------------------------------------------------
-- Concrete source calibration rows.

oneTritNegative :
  toInteger (eval (Trit.neg ∷ [])) ≡ (+ 0) -ℤ (+ 1)
oneTritNegative = refl

oneTritZero :
  toInteger (eval (Trit.zer ∷ [])) ≡ (+ 0) -ℤ (+ 0)
oneTritZero = refl

oneTritPositive :
  toInteger (eval (Trit.pos ∷ [])) ≡ (+ 1) -ℤ (+ 0)
oneTritPositive = refl

threeTritExtremalPositiveWeight :
  eval (Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ [])
  ≡ signedWeight 13 0
threeTritExtremalPositiveWeight = refl

threeTritExtremalNegativeWeight :
  eval (Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ [])
  ≡ signedWeight 0 13
threeTritExtremalNegativeWeight = refl

record BalancedTernaryIntegerBoundary : Set where
  constructor balancedTernaryIntegerBoundary
  field
    positionalWeightsArePowersOfThree : Bool
    digitwiseNegationIsLedgerSwap : Bool
    concreteThreeTritSpanIsMinus13To13 : Bool

canonicalBalancedTernaryIntegerBoundary : BalancedTernaryIntegerBoundary
canonicalBalancedTernaryIntegerBoundary =
  balancedTernaryIntegerBoundary true true true
