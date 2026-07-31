module DASHI.Physics.YangMills.BalabanClayGate4Equation189PhysicalAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4TOperationSmallFactorReductionExact as Reduction

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Target locator: equation (1.89), p. 387. Exact constants and hypotheses remain
-- pending direct primary-page verification. This module proves the finite
-- implication once the pointwise physical suppression and target convention are
-- supplied.
------------------------------------------------------------------------

record PhysicalEquation189Data
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    order : T.FiniteTOperationOrderLaws dataSet
    transitive : ∀ {left middle right} →
      T.LessEqual order left middle →
      T.LessEqual order middle right →
      T.LessEqual order left right

    referenceNormalization : Reference.TReferenceFibreNormalization dataSet

    pointwisePhysicalSuppression :
      ∀ (scale : Scale) (component : Component)
        (slow : SlowField) (fine : Fine) →
      T.LessEqual order
        (Integral.selectedWith (T.sumData dataSet)
          (T.localIntegrand dataSet scale component slow
            (T.oneFunctional dataSet)) slow fine)
        (Integral.selectedWith (T.sumData dataSet)
          (Reference.referenceIntegrand referenceNormalization
            scale component slow) slow fine)

open PhysicalEquation189Data public

normalizedReferenceFibreOrderBound :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (physical : PhysicalEquation189Data dataSet)
    scale component slow →
  T.LessEqual (order physical)
    (Integral.foldSelected (T.sumData dataSet)
      (Integral.selectedWith (T.sumData dataSet)
        (Reference.referenceIntegrand
          (referenceNormalization physical) scale component slow) slow)
      slow (T.fastFibre dataSet scale component))
    (Reference.suppression (referenceNormalization physical) scale)
normalizedReferenceFibreOrderBound {dataSet = dataSet} physical
  scale component slow =
  subst
    (λ lower → T.LessEqual (order physical) lower
      (Reference.suppression (referenceNormalization physical) scale))
    (sym (Reference.referenceFibreAtFastFibreExact
      (referenceNormalization physical) scale component slow))
    (T.reflexive (order physical)
      (Reference.suppression (referenceNormalization physical) scale))

physicalPointwiseSuppressionData :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar} →
  PhysicalEquation189Data dataSet →
  Reduction.TOperationPointwiseSuppressionData dataSet
physicalPointwiseSuppressionData physical = record
  { order = order physical
  ; transitive = transitive physical
  ; referenceIntegrand =
      Reference.referenceIntegrand (referenceNormalization physical)
  ; suppression =
      Reference.suppression (referenceNormalization physical)
  ; pointwiseLargeFieldSuppression = pointwisePhysicalSuppression physical
  ; normalizedSuppressedReferenceFibre =
      normalizedReferenceFibreOrderBound physical
  }

physicalTOperationSmallFactor :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (physical : PhysicalEquation189Data dataSet)
    scale
    (selected : T.SecondClassComponent (T.classData dataSet) scale)
    slow →
  T.LessEqual (order physical)
    (T.localizedTOperation dataSet scale selected slow
      (T.oneFunctional dataSet))
    (Reference.suppression (referenceNormalization physical) scale)
physicalTOperationSmallFactor physical =
  Reduction.tOperationSmallFactorFromPointwiseSuppression
    (physicalPointwiseSuppressionData physical)

normalizedReferenceOrderAssemblyLevel : ProofLevel
normalizedReferenceOrderAssemblyLevel = machineChecked

physicalEquation189ReductionLevel : ProofLevel
physicalEquation189ReductionLevel = machineChecked

-- Only the pointwise comparison remains physical here. The finite fold,
-- normalization, and passage to the T-operation bound are exact.
equation189PointwisePhysicalSuppressionInputsLevel : ProofLevel
equation189PointwisePhysicalSuppressionInputsLevel = conditional

primaryEquation189ConstantVerificationInputsLevel : ProofLevel
primaryEquation189ConstantVerificationInputsLevel = conditional
