module DASHI.Physics.YangMills.BalabanFiniteRangeBlockDecomposition where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

record FiniteRangeBlockDecomposition (Site Kernel Scalar : Set) : Set₁ where
  field
    fullKernel : Site → Site → Scalar
    shellKernel : Nat → Site → Site → Scalar
    zero : Scalar
    add : Scalar → Scalar → Scalar
    rangeBound : Nat → Nat
    DistanceLessEqual : Site → Site → Nat → Set
    finiteRange :
      ∀ shell left right →
      DistanceLessEqual left right (rangeBound shell) → Set
    partialSum : Nat → Site → Site → Scalar
    partialSumDefinition :
      ∀ shell left right →
      partialSum (Agda.Builtin.Nat.suc shell) left right
        ≡ add (partialSum shell left right) (shellKernel shell left right)

open FiniteRangeBlockDecomposition public
