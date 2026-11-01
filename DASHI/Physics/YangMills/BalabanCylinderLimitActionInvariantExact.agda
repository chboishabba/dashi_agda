{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact where

------------------------------------------------------------------------
-- FINITE ACTION/GAUGE INVARIANCE -> CONTINUUM CYLINDER-LIMIT INVARIANCE
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder

record CylinderActionInvariantInputs
    {Observable Scalar : Set}
    {algebra : Cylinder.ScalarCylinderLimitAlgebra Scalar}
    (cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable Scalar algebra)
    (Action : Set) : Set₁ where
  field
    act : Action → Observable → Observable

    finiteActionInvariant :
      ∀ cutoff action observable →
      Cylinder.finiteExpectation cylinder cutoff
        (act action observable)
      ≡
      Cylinder.finiteExpectation cylinder cutoff observable

open CylinderActionInvariantInputs public

continuumActionInvariant :
  ∀ {Observable Scalar algebra cylinder Action}
    (inputs :
      CylinderActionInvariantInputs
        {Observable = Observable} {Scalar = Scalar}
        {algebra = algebra} cylinder Action)
    action observable →
  Cylinder.limitExpectation cylinder
    (act inputs action observable)
  ≡
  Cylinder.limitExpectation cylinder observable
continuumActionInvariant
    {algebra = algebra} {cylinder = cylinder}
    inputs action observable =
  Cylinder.convergenceUnique algebra
    (λ cutoff →
      Cylinder.finiteExpectation cylinder cutoff
        (act inputs action observable))
    (Cylinder.limitExpectation cylinder
      (act inputs action observable))
    (Cylinder.limitExpectation cylinder observable)
    (Cylinder.selectedConverges cylinder
      (act inputs action observable))
    (Cylinder.convergencePointwiseCongruent algebra
      (λ cutoff →
        Cylinder.finiteExpectation cylinder cutoff
          (act inputs action observable))
      (λ cutoff →
        Cylinder.finiteExpectation cylinder cutoff observable)
      (Cylinder.limitExpectation cylinder observable)
      (finiteActionInvariant inputs action observable)
      (Cylinder.selectedConverges cylinder observable))

cylinderActionInvariantLimitCompilerLevel : ProofLevel
cylinderActionInvariantLimitCompilerLevel = machineChecked

-- The physical input is only the finite Wilson/Balaban action or gauge
-- invariance on the SAME normalized finite expectation sequence.
literalFiniteGaugeActionInvarianceLevel : ProofLevel
literalFiniteGaugeActionInvarianceLevel = conditional
