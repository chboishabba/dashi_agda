module DASHI.Physics.YangMills.BalabanClayGate4T3SelfAdjointFormNormReuseExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3
import DASHI.Physics.YangMills.BalabanClayGate4T3ConstrainedHessianRestrictionReuseExact as T3Restriction
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedHessianRestrictionExact as Restriction
import DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact as FormNorm

------------------------------------------------------------------------
-- T3 restricted form-to-operator bridge.
--
-- The existing T3 owner supplies the physical/reference Hessian split and a
-- five-channel relative quadratic-form budget.  For the restricted remainder,
-- a form estimate becomes an operator-norm estimate once the two Hessians are
-- self-adjoint in the selected physical inner product and P* R P is the
-- symmetric restriction.  This module attaches that standard finite theorem
-- directly to T3 without silently treating epsilonTotal as an operator norm.
------------------------------------------------------------------------

record T3SelfAdjointFormNormInputs
    (Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set)
    : Set₁ where
  field
    restrictionInputs : T3Restriction.T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse

    scale : Scale
    volume : Volume
    regime : PatchRegime
    background : Background

    normData : FormNorm.SelfAdjointFormOperatorNormData
      (Fluctuation → Fluctuation) Fluctuation Bound

    selfAdjointData : FormNorm.RestrictedHessianSelfAdjointness
      (Fluctuation → Fluctuation)

    physicalHessianMeaning :
      FormNorm.physicalHessian selfAdjointData
      ≡ T3.physicalFluctuationHessian
          (T3Restriction.t3 restrictionInputs)
          scale volume regime background

    referenceHessianMeaning :
      FormNorm.referenceHessian selfAdjointData
      ≡ T3.referenceHessian
          (T3Restriction.t3 restrictionInputs)
          (T3.makeIndex
            (T3Restriction.t3 restrictionInputs)
            scale volume regime background)

    ambientRemainderMeaning :
      FormNorm.remainder selfAdjointData
      ≡ T3.backgroundHessianRemainder
          (T3Restriction.t3 restrictionInputs)
          (T3.makeIndex
            (T3Restriction.t3 restrictionInputs)
            scale volume regime background)

    restrictedRemainderMeaning :
      FormNorm.restrictedRemainder selfAdjointData
      ≡ Restriction.restrictedPerturbationHessian
          (T3Restriction.restrictionAt restrictionInputs
            scale volume regime background)

    epsilonForm : Bound

    restrictedQuadraticFormBound : ∀ fluctuation →
      FormNorm.UnitState normData fluctuation →
      FormNorm.LessEqual normData
        (FormNorm.absolute normData
          (FormNorm.inner normData fluctuation
            (FormNorm.apply normData
              (FormNorm.restrictedRemainder selfAdjointData)
              fluctuation)))
        epsilonForm

open T3SelfAdjointFormNormInputs public

asRestrictedFormToOperatorNormMeaning :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse}
    (inputs : T3SelfAdjointFormNormInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse) →
  FormNorm.RestrictedFormToOperatorNormMeaning
    (Fluctuation → Fluctuation) Fluctuation Bound
asRestrictedFormToOperatorNormMeaning inputs = record
  { normData = normData inputs
  ; selfAdjointData = selfAdjointData inputs
  ; restrictedOperatorsAgree = refl
  ; epsilonForm = epsilonForm inputs
  ; restrictedQuadraticFormBound = restrictedQuadraticFormBound inputs
  }

restrictedT3FormBoundImpliesOperatorNormBound :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse}
    (inputs : T3SelfAdjointFormNormInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse) →
  FormNorm.LessEqual (normData inputs)
    (FormNorm.operatorNorm (normData inputs)
      (FormNorm.restrictedRemainder (selfAdjointData inputs)))
    (epsilonForm inputs)
restrictedT3FormBoundImpliesOperatorNormBound inputs =
  FormNorm.restrictedSelfAdjointFormBoundImpliesOperatorNormBound
    (asRestrictedFormToOperatorNormMeaning inputs)

t3SelfAdjointFormNormAttachmentLevel : ProofLevel
t3SelfAdjointFormNormAttachmentLevel = machineChecked

t3RestrictedFormToOperatorNormLevel : ProofLevel
t3RestrictedFormToOperatorNormLevel = machineChecked

physicalT3HessianSelfAdjointnessInputsLevel : ProofLevel
physicalT3HessianSelfAdjointnessInputsLevel = conditional

physicalT3RestrictedFormAbsoluteBoundInputsLevel : ProofLevel
physicalT3RestrictedFormAbsoluteBoundInputsLevel = conditional

physicalT3InnerProductNormIdentificationInputsLevel : ProofLevel
physicalT3InnerProductNormIdentificationInputsLevel = conditional
