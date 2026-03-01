module DASHI.Physics.WitnessSetPolicy where

open import Level using (Level; suc)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)

_≥_ : Nat → Nat → Set
m ≥ n = n ≤ m

-- Policy for admissible witness sets used in closure claims.
record WitnessSetPolicy {ℓ} (W : Set ℓ) : Set (suc ℓ) where
  field
    minForward : Nat
    minBackward : Nat
    forwardCount : W → Nat
    backwardCount : W → Nat
    quotaPreserving : W → Set

  admissible : W → Set
  admissible w =
    (forwardCount w ≥ minForward) ×
    (backwardCount w ≥ minBackward) ×
    quotaPreserving w

open WitnessSetPolicy public
