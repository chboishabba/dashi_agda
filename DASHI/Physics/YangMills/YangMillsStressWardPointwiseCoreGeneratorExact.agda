{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsStressWardPointwiseCoreGeneratorExact where

------------------------------------------------------------------------
-- C / POINTWISE COMMON-CORE WARD IDENTITY -> SAME CLOSED GENERATOR
--
-- A physical Ward theorem is naturally pointwise on local vectors:
--
--   q psi = h psi.
--
-- Requiring literal equality of the functions q and h adds an unnecessary
-- function-extensionality seam.  For operator closure the useful standard
-- theorem is instead extensionality of closure under pointwise equality on the
-- same domain.  This owner uses exactly that form.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PointwiseCommonCoreClosureCalculus : Set₁ where
  field
    Core Vector Operator : Set
    close : (Core → Vector) → Operator

    closeRespectsPointwiseEquality :
      ∀ (left right : Core → Vector) →
      (∀ vector → left vector ≡ right vector) →
      close left ≡ close right

open PointwiseCommonCoreClosureCalculus public

record PointwiseStressOSCommonCoreData
    (C : PointwiseCommonCoreClosureCalculus) : Set₁ where
  field
    stressCoreAction : Core C → Vector C
    osCoreAction : Core C → Vector C

    stressOperator osHamiltonian : Operator C

    pointwiseCommonCoreWard :
      ∀ vector →
      stressCoreAction vector ≡ osCoreAction vector

    stressIsClosureOfCoreAction :
      stressOperator ≡ close C stressCoreAction

    osHamiltonianIsClosureOfCoreAction :
      osHamiltonian ≡ close C osCoreAction

open PointwiseStressOSCommonCoreData public

pointwiseCommonCoreWardImpliesSameGenerator :
  (C : PointwiseCommonCoreClosureCalculus) →
  (dataSet : PointwiseStressOSCommonCoreData C) →
  stressOperator dataSet ≡ osHamiltonian dataSet
pointwiseCommonCoreWardImpliesSameGenerator C dataSet =
  trans
    (stressIsClosureOfCoreAction dataSet)
    (trans
      (closeRespectsPointwiseEquality C
        (stressCoreAction dataSet)
        (osCoreAction dataSet)
        (pointwiseCommonCoreWard dataSet))
      (sym (osHamiltonianIsClosureOfCoreAction dataSet)))

pointwiseCommonCoreClosureCompilerLevel : ProofLevel
pointwiseCommonCoreClosureCompilerLevel = machineChecked

-- Standard operator theory: closure is insensitive to pointwise-equal operators
-- on the identical domain/core.  No global function-extensionality axiom is
-- required by the consumer interface.
closureRespectsSameDomainPointwiseEqualityLevel : ProofLevel
closureRespectsSameDomainPointwiseEqualityLevel = standardImported

-- Physical residual: prove the actual local Ward identity pointwise and prove
-- that the stress/OS operators are the corresponding self-adjoint closures.
physicalPointwiseWardAndClosureIdentificationLevel : ProofLevel
physicalPointwiseWardAndClosureIdentificationLevel = conditional
