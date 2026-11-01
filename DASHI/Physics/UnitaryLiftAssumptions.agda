module DASHI.Physics.UnitaryLiftAssumptions where

open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤)

record UnitaryLift : Set₁ where
  field
    Ω   : Set
    H   : Set
    Op  : Set
    U   : Nat → Op
    πsupp : H → Set
    destructive-interference : ⊤
