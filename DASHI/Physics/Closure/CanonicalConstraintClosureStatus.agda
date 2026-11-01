module DASHI.Physics.Closure.CanonicalConstraintClosureStatus where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Constraints.ConcreteInstance as CI

data CanonicalConstraintClosureState : Set where
  concreteThreeGeneratorClosure : CanonicalConstraintClosureState

record CanonicalConstraintClosureStatus : Set where
  field
    generatorCount : Nat
    state : CanonicalConstraintClosureState

canonicalConstraintClosureStatus : CanonicalConstraintClosureStatus
canonicalConstraintClosureStatus =
  record
    { generatorCount = 3
    ; state = concreteThreeGeneratorClosure
    }
