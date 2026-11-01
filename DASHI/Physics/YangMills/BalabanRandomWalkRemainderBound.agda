module DASHI.Physics.YangMills.BalabanRandomWalkRemainderBound where

open import Agda.Builtin.Nat using (Nat)

record RandomWalkRemainderBound (Scalar Bound : Set) : Set₁ where
  field
    remainder : Nat → Scalar
    norm : Scalar → Bound
    majorant : Nat → Bound
    LessEqual : Bound → Bound → Set
    bound : ∀ depth → LessEqual (norm (remainder depth)) (majorant depth)

open RandomWalkRemainderBound public
