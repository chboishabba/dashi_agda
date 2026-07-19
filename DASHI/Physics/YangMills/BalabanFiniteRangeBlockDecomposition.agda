module DASHI.Physics.YangMills.BalabanFiniteRangeBlockDecomposition where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

record FiniteRangeBlockDecomposition (Site Kernel Scalar : Set) : Set₁ where
  field
    fullKernel : Site → Site → Scalar
    shellKernel : Nat → Site → Site → Scalar
    shellWitness : Nat → Kernel
    zero : Scalar
    add : Scalar → Scalar → Scalar
    rangeBound : Nat → Nat
    OutsideRange : Site → Site → Nat → Set
    finiteRange :
      ∀ shell left right →
      OutsideRange left right (rangeBound shell) →
      shellKernel shell left right ≡ zero
    partialSum : Nat → Site → Site → Scalar
    partialSumDefinition :
      ∀ shell left right →
      partialSum (suc shell) left right
        ≡ add (partialSum shell left right) (shellKernel shell left right)

open FiniteRangeBlockDecomposition public
