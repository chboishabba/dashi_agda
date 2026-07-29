module DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Factors
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4Equation189PhysicalAssemblyExact as Equation189

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I. The Basic Step of the R Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- This module does not infer a relative density estimate from the existing
-- absolute 1/16 activity bound. It requires six named physical/reference
-- comparisons and proves that their product gives the pointwise T comparison.
------------------------------------------------------------------------

record RelativeSixFactorComparison (Scale Traversal : Set) : Set₁ where
  field
    physical : Factors.WilsonTraversalActivityFactors Scale Traversal

    referenceAction referenceJacobian referenceDeterminant referenceBCH
      referenceLocalization referencePatch : Scale → Traversal → ℚ

    referenceActionNonnegative : ∀ scale traversal →
      0ℚ ≤ referenceAction scale traversal
    referenceJacobianNonnegative : ∀ scale traversal →
      0ℚ ≤ referenceJacobian scale traversal
    referenceDeterminantNonnegative : ∀ scale traversal →
      0ℚ ≤ referenceDeterminant scale traversal
    referenceBCHNonnegative : ∀ scale traversal →
      0ℚ ≤ referenceBCH scale traversal
    referenceLocalizationNonnegative : ∀ scale traversal →
      0ℚ ≤ referenceLocalization scale traversal
    referencePatchNonnegative : ∀ scale traversal →
      0ℚ ≤ referencePatch scale traversal

    actionRelative : ∀ scale traversal →
      Factors.actionFactor physical scale traversal
      ≤ referenceAction scale traversal
    jacobianRelative : ∀ scale traversal →
      Factors.jacobianFactor physical scale traversal
      ≤ referenceJacobian scale traversal
    determinantRelative : ∀ scale traversal →
      Factors.determinantFactor physical scale traversal
      ≤ referenceDeterminant scale traversal
    bchRelative : ∀ scale traversal →
      Factors.bchFactor physical scale traversal
      ≤ referenceBCH scale traversal
    localizationRelative : ∀ scale traversal →
      Factors.localizationFactor physical scale traversal
      ≤ referenceLocalization scale traversal
    patchRelative : ∀ scale traversal →
      Factors.patchFactor physical scale traversal
      ≤ referencePatch scale traversal

open RelativeSixFactorComparison public

referenceProduct :
  ∀ {Scale Traversal} →
  RelativeSixFactorComparison Scale Traversal → Scale → Traversal → ℚ
referenceProduct dataSet scale traversal =
  referenceAction dataSet scale traversal
  * (referenceJacobian dataSet scale traversal
  * (referenceDeterminant dataSet scale traversal
  * (referenceBCH dataSet scale traversal
  * (referenceLocalization dataSet scale traversal
  * referencePatch dataSet scale traversal))))

referenceLocalizationPatchNonnegative :
  ∀ {Scale Traversal}
    (dataSet : RelativeSixFactorComparison Scale Traversal)
    scale traversal →
  0ℚ ≤ referenceLocalization dataSet scale traversal
    * referencePatch dataSet scale traversal
referenceLocalizationPatchNonnegative dataSet scale traversal =
  Factors.multiplyNonnegative (physical dataSet)
    (referenceLocalizationNonnegative dataSet scale traversal)
    (referencePatchNonnegative dataSet scale traversal)

referenceBCHTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : RelativeSixFactorComparison Scale Traversal)
    scale traversal →
  0ℚ ≤ referenceBCH dataSet scale traversal
    * (referenceLocalization dataSet scale traversal
      * referencePatch dataSet scale traversal)
referenceBCHTailNonnegative dataSet scale traversal =
  Factors.multiplyNonnegative (physical dataSet)
    (referenceBCHNonnegative dataSet scale traversal)
    (referenceLocalizationPatchNonnegative dataSet scale traversal)

referenceDeterminantTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : RelativeSixFactorComparison Scale Traversal)
    scale traversal →
  0ℚ ≤ referenceDeterminant dataSet scale traversal
    * (referenceBCH dataSet scale traversal
      * (referenceLocalization dataSet scale traversal
        * referencePatch dataSet scale traversal))
referenceDeterminantTailNonnegative dataSet scale traversal =
  Factors.multiplyNonnegative (physical dataSet)
    (referenceDeterminantNonnegative dataSet scale traversal)
    (referenceBCHTailNonnegative dataSet scale traversal)

referenceJacobianTailNonnegative :
  ∀ {Scale Traversal}
    (dataSet : RelativeSixFactorComparison Scale Traversal)
    scale traversal →
  0ℚ ≤ referenceJacobian dataSet scale traversal
    * (referenceDeterminant dataSet scale traversal
      * (referenceBCH dataSet scale traversal
        * (referenceLocalization dataSet scale traversal
          * referencePatch dataSet scale traversal)))
referenceJacobianTailNonnegative dataSet scale traversal =
  Factors.multiplyNonnegative (physical dataSet)
    (referenceJacobianNonnegative dataSet scale traversal)
    (referenceDeterminantTailNonnegative dataSet scale traversal)

physicalProductBelowReferenceProduct :
  ∀ {Scale Traversal}
    (dataSet : RelativeSixFactorComparison Scale Traversal)
    scale traversal →
  Factors.actionFactor (physical dataSet) scale traversal
    * (Factors.jacobianFactor (physical dataSet) scale traversal
    * (Factors.determinantFactor (physical dataSet) scale traversal
    * (Factors.bchFactor (physical dataSet) scale traversal
    * (Factors.localizationFactor (physical dataSet) scale traversal
    * Factors.patchFactor (physical dataSet) scale traversal))))
  ≤ referenceProduct dataSet scale traversal
physicalProductBelowReferenceProduct dataSet scale traversal =
  Factors.multiplyMonotoneNonnegative (physical dataSet)
    (Factors.actionFactorNonnegative (physical dataSet) scale traversal)
    (referenceActionNonnegative dataSet scale traversal)
    (Factors.physicalJacobianTailNonnegative (physical dataSet) scale traversal)
    (referenceJacobianTailNonnegative dataSet scale traversal)
    (actionRelative dataSet scale traversal)
    (Factors.multiplyMonotoneNonnegative (physical dataSet)
      (Factors.jacobianFactorNonnegative (physical dataSet) scale traversal)
      (referenceJacobianNonnegative dataSet scale traversal)
      (Factors.physicalDeterminantTailNonnegative
        (physical dataSet) scale traversal)
      (referenceDeterminantTailNonnegative dataSet scale traversal)
      (jacobianRelative dataSet scale traversal)
      (Factors.multiplyMonotoneNonnegative (physical dataSet)
        (Factors.determinantFactorNonnegative
          (physical dataSet) scale traversal)
        (referenceDeterminantNonnegative dataSet scale traversal)
        (Factors.physicalBCHTailNonnegative
          (physical dataSet) scale traversal)
        (referenceBCHTailNonnegative dataSet scale traversal)
        (determinantRelative dataSet scale traversal)
        (Factors.multiplyMonotoneNonnegative (physical dataSet)
          (Factors.bchFactorNonnegative (physical dataSet) scale traversal)
          (referenceBCHNonnegative dataSet scale traversal)
          (Factors.physicalLocalizationPatchNonnegative
            (physical dataSet) scale traversal)
          (referenceLocalizationPatchNonnegative dataSet scale traversal)
          (bchRelative dataSet scale traversal)
          (Factors.multiplyMonotoneNonnegative (physical dataSet)
            (Factors.localizationFactorNonnegative
              (physical dataSet) scale traversal)
            (referenceLocalizationNonnegative dataSet scale traversal)
            (Factors.patchFactorNonnegative
              (physical dataSet) scale traversal)
            (referencePatchNonnegative dataSet scale traversal)
            (localizationRelative dataSet scale traversal)
            (patchRelative dataSet scale traversal)))))

physicalActivityBelowReferenceProduct :
  ∀ {Scale Traversal}
    (dataSet : RelativeSixFactorComparison Scale Traversal)
    scale traversal →
  Factors.activity (physical dataSet) scale traversal
  ≤ referenceProduct dataSet scale traversal
physicalActivityBelowReferenceProduct dataSet scale traversal =
  Factors.transitive (physical dataSet)
    (Factors.activityBelowPhysicalProduct (physical dataSet) scale traversal)
    (physicalProductBelowReferenceProduct dataSet scale traversal)

record RelativeTPointwiseMeaning
    {Scale Fine SlowField Component Functional Traversal : Set}
    (tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ)
    (comparison : RelativeSixFactorComparison Scale Traversal) : Set₁ where
  field
    order : T.FiniteTOperationOrderLaws tData
    orderTransitive : ∀ {left middle right} →
      T.LessEqual order left middle →
      T.LessEqual order middle right →
      T.LessEqual order left right
    rationalOrderImpliesTOperationOrder : ∀ {left right} →
      left ≤ right → T.LessEqual order left right

    traversalOf : Scale → Component → SlowField → Fine → Traversal

    oneIntegrandMeaning : ∀ scale component slow fine →
      T.localIntegrand tData scale component slow
        (T.oneFunctional tData) fine
      ≡ Factors.activity (physical comparison) scale
          (traversalOf scale component slow fine)

    referenceNormalization : Reference.TReferenceFibreNormalization tData

    referenceIntegrandMeaning : ∀ scale component slow fine →
      Reference.referenceIntegrand referenceNormalization
        scale component slow fine
      ≡ referenceProduct comparison scale
          (traversalOf scale component slow fine)

open RelativeTPointwiseMeaning public

unselectedRelativePointwise :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : RelativeSixFactorComparison Scale Traversal}
    (meaning : RelativeTPointwiseMeaning tData comparison)
    scale component slow fine →
  T.LessEqual (order meaning)
    (T.localIntegrand tData scale component slow
      (T.oneFunctional tData) fine)
    (Reference.referenceIntegrand
      (referenceNormalization meaning) scale component slow fine)
unselectedRelativePointwise {comparison = comparison} meaning
  scale component slow fine =
  subst
    (λ lower → T.LessEqual (order meaning) lower
      (Reference.referenceIntegrand
        (referenceNormalization meaning) scale component slow fine))
    (sym (oneIntegrandMeaning meaning scale component slow fine))
    (subst
      (λ upper → T.LessEqual (order meaning)
        (Factors.activity (physical comparison) scale
          (traversalOf meaning scale component slow fine)) upper)
      (sym (referenceIntegrandMeaning meaning scale component slow fine))
      (rationalOrderImpliesTOperationOrder meaning
        (physicalActivityBelowReferenceProduct comparison scale
          (traversalOf meaning scale component slow fine))))

selectedRelativePointwise :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : RelativeSixFactorComparison Scale Traversal}
    (meaning : RelativeTPointwiseMeaning tData comparison)
    scale component slow fine →
  T.LessEqual (order meaning)
    (Integral.selectedWith (T.sumData tData)
      (T.localIntegrand tData scale component slow
        (T.oneFunctional tData)) slow fine)
    (Integral.selectedWith (T.sumData tData)
      (Reference.referenceIntegrand
        (referenceNormalization meaning) scale component slow) slow fine)
selectedRelativePointwise {tData = tData} meaning
  scale component slow fine
  with Integral.coarseMatches (T.sumData tData) fine slow
... | false = T.reflexive (order meaning) (Integral.zero (T.sumData tData))
... | true = unselectedRelativePointwise meaning scale component slow fine

asPhysicalEquation189Data :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : RelativeSixFactorComparison Scale Traversal} →
  RelativeTPointwiseMeaning tData comparison →
  Equation189.PhysicalEquation189Data tData
asPhysicalEquation189Data meaning = record
  { Equation189.PhysicalEquation189Data.order = order meaning
  ; Equation189.PhysicalEquation189Data.transitive = orderTransitive meaning
  ; Equation189.PhysicalEquation189Data.referenceNormalization =
      referenceNormalization meaning
  ; Equation189.PhysicalEquation189Data.pointwisePhysicalSuppression =
      selectedRelativePointwise meaning
  }

relativeSixFactorProductComparisonLevel : ProofLevel
relativeSixFactorProductComparisonLevel = machineChecked

relativeTPointwiseSelectionLevel : ProofLevel
relativeTPointwiseSelectionLevel = machineChecked

relativeTEquation189AdapterLevel : ProofLevel
relativeTEquation189AdapterLevel = machineChecked

physicalActionRelativeReferenceInputsLevel : ProofLevel
physicalActionRelativeReferenceInputsLevel = conditional

physicalJacobianRelativeReferenceInputsLevel : ProofLevel
physicalJacobianRelativeReferenceInputsLevel = conditional

physicalDeterminantRelativeReferenceInputsLevel : ProofLevel
physicalDeterminantRelativeReferenceInputsLevel = conditional

physicalBCHRelativeReferenceInputsLevel : ProofLevel
physicalBCHRelativeReferenceInputsLevel = conditional

physicalLocalizationRelativeReferenceInputsLevel : ProofLevel
physicalLocalizationRelativeReferenceInputsLevel = conditional

physicalPatchRelativeReferenceInputsLevel : ProofLevel
physicalPatchRelativeReferenceInputsLevel = conditional

physicalReferenceIntegrandMeaningInputsLevel : ProofLevel
physicalReferenceIntegrandMeaningInputsLevel = conditional
