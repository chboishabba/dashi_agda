module MonsterMask where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List

------------------------------------------------------------------------
-- We model the 15 prime-power factors of |M| as positions 0..14.

FactorCount : Nat
FactorCount = 15

------------------------------------------------------------------------
-- A mask is a length-15 boolean list:
-- true  = keep factor
-- false = remove factor

Mask : Set
Mask = List Bool

replicate : Nat → Bool → Mask
replicate zero    b = []
replicate (suc n) b = b ∷ replicate n b

boolAnd : Bool → Bool → Bool
boolAnd true true = true
boolAnd _    _    = false

notBool : Bool → Bool
notBool true  = false
notBool false = true

------------------------------------------------------------------------
-- Canonical full mask (all factors kept)

fullMask : Mask
fullMask = replicate FactorCount true

------------------------------------------------------------------------
-- Collapse mask: remove everything

emptyMask : Mask
emptyMask = replicate FactorCount false

------------------------------------------------------------------------
-- Pointwise AND (factor removal composition)

_∧_ : Mask → Mask → Mask
[] ∧ [] = []
(b ∷ xs) ∧ (c ∷ ys) = boolAnd b c ∷ (xs ∧ ys)
_ ∧ _ = []

------------------------------------------------------------------------
-- Kernel-style operator: remove a fixed subset F

record Kernel : Set where
  field
    K : Mask → Mask

------------------------------------------------------------------------
-- Example: projection to a fixed group representative mask

projectTo : Mask → Kernel
projectTo target = record
  { K = λ _ → target
  }

------------------------------------------------------------------------
-- Involution: flip keep/remove

flipMask : Mask → Mask
flipMask [] = []
flipMask (b ∷ xs) = notBool b ∷ flipMask xs
