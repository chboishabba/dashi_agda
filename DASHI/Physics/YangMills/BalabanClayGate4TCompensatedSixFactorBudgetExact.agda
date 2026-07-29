module DASHI.Physics.YangMills.BalabanClayGate4TCompensatedSixFactorBudgetExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Factors
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
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
-- Haar, determinant, BCH, localization and patch factors need not each be
-- bounded by the corresponding reference factor. Their losses may be paid for
-- by the large-plaquette action gain. The finite theorem below first reuses the
-- six-factor product comparison with multiplier-weighted reference factors,
-- then regroups all multipliers and applies one residual budget inequality.
------------------------------------------------------------------------

record CompensatedSixFactorComparison (Scale Traversal : Set) : Set₁ where
  field
    physical : Factors.WilsonTraversalActivityFactors Scale Traversal

    referenceAction referenceJacobian referenceDeterminant referenceBCH
      referenceLocalization referencePatch : Scale → Traversal → ℚ

    actionGain haarLoss determinantLoss bchLoss localizationLoss patchLoss :
      Scale → Traversal → ℚ

    residualSuppression : Scale → ℚ

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

    actionGainNonnegative : ∀ scale traversal → 0ℚ ≤ actionGain scale traversal
    haarLossNonnegative : ∀ scale traversal → 0ℚ ≤ haarLoss scale traversal
    determinantLossNonnegative : ∀ scale traversal →
      0ℚ ≤ determinantLoss scale traversal
    bchLossNonnegative : ∀ scale traversal → 0ℚ ≤ bchLoss scale traversal
    localizationLossNonnegative : ∀ scale traversal →
      0ℚ ≤ localizationLoss scale traversal
    patchLossNonnegative : ∀ scale traversal → 0ℚ ≤ patchLoss scale traversal
    residualSuppressionNonnegative : ∀ scale → 0ℚ ≤ residualSuppression scale

    actionCompensated : ∀ scale traversal →
      Factors.actionFactor physical scale traversal
      ≤ actionGain scale traversal * referenceAction scale traversal
    jacobianCompensated : ∀ scale traversal →
      Factors.jacobianFactor physical scale traversal
      ≤ haarLoss scale traversal * referenceJacobian scale traversal
    determinantCompensated : ∀ scale traversal →
      Factors.determinantFactor physical scale traversal
      ≤ determinantLoss scale traversal * referenceDeterminant scale traversal
    bchCompensated : ∀ scale traversal →
      Factors.bchFactor physical scale traversal
      ≤ bchLoss scale traversal * referenceBCH scale traversal
    localizationCompensated : ∀ scale traversal →
      Factors.localizationFactor physical scale traversal
      ≤ localizationLoss scale traversal * referenceLocalization scale traversal
    patchCompensated : ∀ scale traversal →
      Factors.patchFactor physical scale traversal
      ≤ patchLoss scale traversal * referencePatch scale traversal

    combinedMultiplierBelowResidual : ∀ scale traversal →
      actionGain scale traversal
      * (haarLoss scale traversal
      * (determinantLoss scale traversal
      * (bchLoss scale traversal
      * (localizationLoss scale traversal
      * patchLoss scale traversal))))
      ≤ residualSuppression scale

open CompensatedSixFactorComparison public

referenceProduct :
  ∀ {Scale Traversal} →
  CompensatedSixFactorComparison Scale Traversal → Scale → Traversal → ℚ
referenceProduct dataSet scale traversal =
  referenceAction dataSet scale traversal
  * (referenceJacobian dataSet scale traversal
  * (referenceDeterminant dataSet scale traversal
  * (referenceBCH dataSet scale traversal
  * (referenceLocalization dataSet scale traversal
  * referencePatch dataSet scale traversal))))

combinedMultiplier :
  ∀ {Scale Traversal} →
  CompensatedSixFactorComparison Scale Traversal → Scale → Traversal → ℚ
combinedMultiplier dataSet scale traversal =
  actionGain dataSet scale traversal
  * (haarLoss dataSet scale traversal
  * (determinantLoss dataSet scale traversal
  * (bchLoss dataSet scale traversal
  * (localizationLoss dataSet scale traversal
  * patchLoss dataSet scale traversal))))

asRelativeSixFactorComparison :
  ∀ {Scale Traversal} →
  CompensatedSixFactorComparison Scale Traversal →
  Relative.RelativeSixFactorComparison Scale Traversal
asRelativeSixFactorComparison dataSet = record
  { Relative.RelativeSixFactorComparison.physical = physical dataSet
  ; Relative.RelativeSixFactorComparison.referenceAction =
      λ scale traversal →
        actionGain dataSet scale traversal * referenceAction dataSet scale traversal
  ; Relative.RelativeSixFactorComparison.referenceJacobian =
      λ scale traversal →
        haarLoss dataSet scale traversal * referenceJacobian dataSet scale traversal
  ; Relative.RelativeSixFactorComparison.referenceDeterminant =
      λ scale traversal →
        determinantLoss dataSet scale traversal
          * referenceDeterminant dataSet scale traversal
  ; Relative.RelativeSixFactorComparison.referenceBCH =
      λ scale traversal →
        bchLoss dataSet scale traversal * referenceBCH dataSet scale traversal
  ; Relative.RelativeSixFactorComparison.referenceLocalization =
      λ scale traversal →
        localizationLoss dataSet scale traversal
          * referenceLocalization dataSet scale traversal
  ; Relative.RelativeSixFactorComparison.referencePatch =
      λ scale traversal →
        patchLoss dataSet scale traversal * referencePatch dataSet scale traversal
  ; Relative.RelativeSixFactorComparison.referenceActionNonnegative =
      λ scale traversal → Factors.multiplyNonnegative (physical dataSet)
        (actionGainNonnegative dataSet scale traversal)
        (referenceActionNonnegative dataSet scale traversal)
  ; Relative.RelativeSixFactorComparison.referenceJacobianNonnegative =
      λ scale traversal → Factors.multiplyNonnegative (physical dataSet)
        (haarLossNonnegative dataSet scale traversal)
        (referenceJacobianNonnegative dataSet scale traversal)
  ; Relative.RelativeSixFactorComparison.referenceDeterminantNonnegative =
      λ scale traversal → Factors.multiplyNonnegative (physical dataSet)
        (determinantLossNonnegative dataSet scale traversal)
        (referenceDeterminantNonnegative dataSet scale traversal)
  ; Relative.RelativeSixFactorComparison.referenceBCHNonnegative =
      λ scale traversal → Factors.multiplyNonnegative (physical dataSet)
        (bchLossNonnegative dataSet scale traversal)
        (referenceBCHNonnegative dataSet scale traversal)
  ; Relative.RelativeSixFactorComparison.referenceLocalizationNonnegative =
      λ scale traversal → Factors.multiplyNonnegative (physical dataSet)
        (localizationLossNonnegative dataSet scale traversal)
        (referenceLocalizationNonnegative dataSet scale traversal)
  ; Relative.RelativeSixFactorComparison.referencePatchNonnegative =
      λ scale traversal → Factors.multiplyNonnegative (physical dataSet)
        (patchLossNonnegative dataSet scale traversal)
        (referencePatchNonnegative dataSet scale traversal)
  ; Relative.RelativeSixFactorComparison.actionRelative = actionCompensated dataSet
  ; Relative.RelativeSixFactorComparison.jacobianRelative =
      jacobianCompensated dataSet
  ; Relative.RelativeSixFactorComparison.determinantRelative =
      determinantCompensated dataSet
  ; Relative.RelativeSixFactorComparison.bchRelative = bchCompensated dataSet
  ; Relative.RelativeSixFactorComparison.localizationRelative =
      localizationCompensated dataSet
  ; Relative.RelativeSixFactorComparison.patchRelative = patchCompensated dataSet
  }

compensatedProductRegroupExact :
  ∀ {Scale Traversal}
    (dataSet : CompensatedSixFactorComparison Scale Traversal)
    scale traversal →
  Relative.referenceProduct (asRelativeSixFactorComparison dataSet)
    scale traversal
  ≡ combinedMultiplier dataSet scale traversal
    * referenceProduct dataSet scale traversal
compensatedProductRegroupExact dataSet scale traversal =
  ℚRing.solve-∀
    (actionGain dataSet scale traversal)
    (referenceAction dataSet scale traversal)
    (haarLoss dataSet scale traversal)
    (referenceJacobian dataSet scale traversal)
    (determinantLoss dataSet scale traversal)
    (referenceDeterminant dataSet scale traversal)
    (bchLoss dataSet scale traversal)
    (referenceBCH dataSet scale traversal)
    (localizationLoss dataSet scale traversal)
    (referenceLocalization dataSet scale traversal)
    (patchLoss dataSet scale traversal)
    (referencePatch dataSet scale traversal)

referenceProductNonnegative :
  ∀ {Scale Traversal}
    (dataSet : CompensatedSixFactorComparison Scale Traversal)
    scale traversal →
  0ℚ ≤ referenceProduct dataSet scale traversal
referenceProductNonnegative dataSet scale traversal =
  Factors.multiplyNonnegative (physical dataSet)
    (referenceActionNonnegative dataSet scale traversal)
    (Factors.multiplyNonnegative (physical dataSet)
      (referenceJacobianNonnegative dataSet scale traversal)
      (Factors.multiplyNonnegative (physical dataSet)
        (referenceDeterminantNonnegative dataSet scale traversal)
        (Factors.multiplyNonnegative (physical dataSet)
          (referenceBCHNonnegative dataSet scale traversal)
          (Factors.multiplyNonnegative (physical dataSet)
            (referenceLocalizationNonnegative dataSet scale traversal)
            (referencePatchNonnegative dataSet scale traversal)))))

combinedMultiplierNonnegative :
  ∀ {Scale Traversal}
    (dataSet : CompensatedSixFactorComparison Scale Traversal)
    scale traversal →
  0ℚ ≤ combinedMultiplier dataSet scale traversal
combinedMultiplierNonnegative dataSet scale traversal =
  Factors.multiplyNonnegative (physical dataSet)
    (actionGainNonnegative dataSet scale traversal)
    (Factors.multiplyNonnegative (physical dataSet)
      (haarLossNonnegative dataSet scale traversal)
      (Factors.multiplyNonnegative (physical dataSet)
        (determinantLossNonnegative dataSet scale traversal)
        (Factors.multiplyNonnegative (physical dataSet)
          (bchLossNonnegative dataSet scale traversal)
          (Factors.multiplyNonnegative (physical dataSet)
            (localizationLossNonnegative dataSet scale traversal)
            (patchLossNonnegative dataSet scale traversal)))))

physicalActivityBelowResidualReference :
  ∀ {Scale Traversal}
    (dataSet : CompensatedSixFactorComparison Scale Traversal)
    scale traversal →
  Factors.activity (physical dataSet) scale traversal
  ≤ residualSuppression dataSet scale * referenceProduct dataSet scale traversal
physicalActivityBelowResidualReference dataSet scale traversal =
  Factors.transitive (physical dataSet)
    (subst
      (λ upper → Factors.activity (physical dataSet) scale traversal ≤ upper)
      (compensatedProductRegroupExact dataSet scale traversal)
      (Relative.physicalActivityBelowReferenceProduct
        (asRelativeSixFactorComparison dataSet) scale traversal))
    (Factors.multiplyMonotoneNonnegative (physical dataSet)
      (combinedMultiplierNonnegative dataSet scale traversal)
      (residualSuppressionNonnegative dataSet scale)
      (referenceProductNonnegative dataSet scale traversal)
      (referenceProductNonnegative dataSet scale traversal)
      (combinedMultiplierBelowResidual dataSet scale traversal)
      (Factors.reflexive (physical dataSet)
        (referenceProduct dataSet scale traversal)))

record CompensatedTPointwiseMeaning
    {Scale Fine SlowField Component Functional Traversal : Set}
    (tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ)
    (comparison : CompensatedSixFactorComparison Scale Traversal) : Set₁ where
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
      ≡ residualSuppression comparison scale
        * referenceProduct comparison
          scale (traversalOf scale component slow fine)

open CompensatedTPointwiseMeaning public

unselectedCompensatedPointwise :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : CompensatedSixFactorComparison Scale Traversal}
    (meaning : CompensatedTPointwiseMeaning tData comparison)
    scale component slow fine →
  T.LessEqual (order meaning)
    (T.localIntegrand tData scale component slow
      (T.oneFunctional tData) fine)
    (Reference.referenceIntegrand
      (referenceNormalization meaning) scale component slow fine)
unselectedCompensatedPointwise {comparison = comparison} meaning
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
        (physicalActivityBelowResidualReference comparison scale
          (traversalOf meaning scale component slow fine))))

selectedCompensatedPointwise :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : CompensatedSixFactorComparison Scale Traversal}
    (meaning : CompensatedTPointwiseMeaning tData comparison)
    scale component slow fine →
  T.LessEqual (order meaning)
    (Integral.selectedWith (T.sumData tData)
      (T.localIntegrand tData scale component slow
        (T.oneFunctional tData)) slow fine)
    (Integral.selectedWith (T.sumData tData)
      (Reference.referenceIntegrand
        (referenceNormalization meaning) scale component slow) slow fine)
selectedCompensatedPointwise {tData = tData} meaning
  scale component slow fine
  with Integral.coarseMatches (T.sumData tData) fine slow
... | false = T.reflexive (order meaning) (Integral.zero (T.sumData tData))
... | true = unselectedCompensatedPointwise meaning scale component slow fine

asPhysicalEquation189Data :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : CompensatedSixFactorComparison Scale Traversal} →
  CompensatedTPointwiseMeaning tData comparison →
  Equation189.PhysicalEquation189Data tData
asPhysicalEquation189Data meaning = record
  { Equation189.PhysicalEquation189Data.order = order meaning
  ; Equation189.PhysicalEquation189Data.transitive = orderTransitive meaning
  ; Equation189.PhysicalEquation189Data.referenceNormalization =
      referenceNormalization meaning
  ; Equation189.PhysicalEquation189Data.pointwisePhysicalSuppression =
      selectedCompensatedPointwise meaning
  }

compensatedSixFactorProductLevel : ProofLevel
compensatedSixFactorProductLevel = machineChecked

compensatedBudgetToPointwiseLevel : ProofLevel
compensatedBudgetToPointwiseLevel = machineChecked

compensatedEquation189AdapterLevel : ProofLevel
compensatedEquation189AdapterLevel = machineChecked

physicalActionGainInputsLevel : ProofLevel
physicalActionGainInputsLevel = conditional

physicalHaarLossInputsLevel : ProofLevel
physicalHaarLossInputsLevel = conditional

physicalDeterminantLossInputsLevel : ProofLevel
physicalDeterminantLossInputsLevel = conditional

physicalBCHLocalizationPatchLossInputsLevel : ProofLevel
physicalBCHLocalizationPatchLossInputsLevel = conditional

primaryEquation189BudgetIdentificationLevel : ProofLevel
primaryEquation189BudgetIdentificationLevel = conditional
