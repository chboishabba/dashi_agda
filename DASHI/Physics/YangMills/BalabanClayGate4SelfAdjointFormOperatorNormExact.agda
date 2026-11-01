module DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Self-adjoint quadratic-form bounds and operator norms.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- For a finite-dimensional self-adjoint operator R,
--
--   ||R|| = sup_{||x||=1} |<x,Rx>|.
--
-- Thus a uniform quadratic-form bound is already an operator-norm bound once
-- self-adjointness and the physical inner-product/norm identification have been
-- proved.  The record keeps those facts proof-bearing rather than treating a
-- form budget as definitionally equal to an operator norm.
------------------------------------------------------------------------

record SelfAdjointFormOperatorNormData
    (Operator State Bound : Set) : Set₁ where
  field
    apply : Operator → State → State
    inner : State → State → Bound
    absolute : Bound → Bound
    operatorNorm : Operator → Bound
    LessEqual : Bound → Bound → Set

    UnitState : State → Set
    SelfAdjoint : Operator → Set

    rayleighOperatorNormUpperBound : ∀ operator epsilon →
      SelfAdjoint operator →
      (∀ state → UnitState state →
        LessEqual
          (absolute (inner state (apply operator state)))
          epsilon) →
      LessEqual (operatorNorm operator) epsilon

open SelfAdjointFormOperatorNormData public

selfAdjointFormBoundImpliesOperatorNormBound :
  ∀ {Operator State Bound}
    (dataSet : SelfAdjointFormOperatorNormData Operator State Bound)
    operator epsilon →
  SelfAdjoint dataSet operator →
  (∀ state → UnitState dataSet state →
    LessEqual dataSet
      (absolute dataSet
        (inner dataSet state (apply dataSet operator state)))
      epsilon) →
  LessEqual dataSet (operatorNorm dataSet operator) epsilon
selfAdjointFormBoundImpliesOperatorNormBound dataSet operator epsilon =
  rayleighOperatorNormUpperBound dataSet operator epsilon

record RestrictedHessianSelfAdjointness
    (Operator : Set) : Set₁ where
  field
    physicalHessian referenceHessian remainder projection
      restrictedRemainder : Operator

    SelfAdjoint : Operator → Set

    physicalHessianSelfAdjoint : SelfAdjoint physicalHessian
    referenceHessianSelfAdjoint : SelfAdjoint referenceHessian

    RemainderIsDifference : Set
    remainderIsDifference : RemainderIsDifference

    remainderDifferenceSelfAdjoint :
      SelfAdjoint physicalHessian →
      SelfAdjoint referenceHessian →
      RemainderIsDifference →
      SelfAdjoint remainder

    RestrictedIsSymmetricProjection : Set
    restrictedIsSymmetricProjection : RestrictedIsSymmetricProjection

    symmetricProjectionPreservesSelfAdjointness :
      SelfAdjoint remainder →
      RestrictedIsSymmetricProjection →
      SelfAdjoint restrictedRemainder

open RestrictedHessianSelfAdjointness public

restrictedRemainderSelfAdjoint :
  ∀ {Operator}
    (dataSet : RestrictedHessianSelfAdjointness Operator) →
  SelfAdjoint dataSet (restrictedRemainder dataSet)
restrictedRemainderSelfAdjoint dataSet =
  symmetricProjectionPreservesSelfAdjointness dataSet
    (remainderDifferenceSelfAdjoint dataSet
      (physicalHessianSelfAdjoint dataSet)
      (referenceHessianSelfAdjoint dataSet)
      (remainderIsDifference dataSet))
    (restrictedIsSymmetricProjection dataSet)

record RestrictedFormToOperatorNormMeaning
    (Operator State Bound : Set) : Set₁ where
  field
    normData : SelfAdjointFormOperatorNormData Operator State Bound
    selfAdjointData : RestrictedHessianSelfAdjointness Operator

    restrictedSelfAdjointMeaning :
      SelfAdjoint normData (restrictedRemainder selfAdjointData)

    epsilonForm : Bound

    restrictedQuadraticFormBound : ∀ state →
      UnitState normData state →
      LessEqual normData
        (absolute normData
          (inner normData state
            (apply normData
              (restrictedRemainder selfAdjointData) state)))
        epsilonForm

open RestrictedFormToOperatorNormMeaning public

restrictedSelfAdjointFormBoundImpliesOperatorNormBound :
  ∀ {Operator State Bound}
    (meaning : RestrictedFormToOperatorNormMeaning
      Operator State Bound) →
  LessEqual (normData meaning)
    (operatorNorm (normData meaning)
      (restrictedRemainder (selfAdjointData meaning)))
    (epsilonForm meaning)
restrictedSelfAdjointFormBoundImpliesOperatorNormBound meaning =
  selfAdjointFormBoundImpliesOperatorNormBound
    (normData meaning)
    (restrictedRemainder (selfAdjointData meaning))
    (epsilonForm meaning)
    (restrictedSelfAdjointMeaning meaning)
    (restrictedQuadraticFormBound meaning)

selfAdjointRayleighCharacterizationLevel : ProofLevel
selfAdjointRayleighCharacterizationLevel = standardImported

restrictedRemainderSelfAdjointAssemblyLevel : ProofLevel
restrictedRemainderSelfAdjointAssemblyLevel = machineChecked

restrictedFormToOperatorNormAssemblyLevel : ProofLevel
restrictedFormToOperatorNormAssemblyLevel = machineChecked

physicalHessianSelfAdjointnessInputsLevel : ProofLevel
physicalHessianSelfAdjointnessInputsLevel = conditional

physicalSymmetricProjectionMeaningInputsLevel : ProofLevel
physicalSymmetricProjectionMeaningInputsLevel = conditional

physicalQuadraticFormAbsoluteBoundInputsLevel : ProofLevel
physicalQuadraticFormAbsoluteBoundInputsLevel = conditional
