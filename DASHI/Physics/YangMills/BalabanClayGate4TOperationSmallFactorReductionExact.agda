module DASHI.Physics.YangMills.BalabanClayGate4TOperationSmallFactorReductionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T

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
-- Target: equation (1.89), p. 387, pending direct theorem-text verification.
-- This module proves the finite integration step. The remaining physical input
-- is exactly the pointwise Wilson/Boltzmann suppression on the second-class fast
-- fibre together with the normalized reference-fibre estimate.
------------------------------------------------------------------------

record TOperationPointwiseSuppressionData
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    order : T.FiniteTOperationOrderLaws dataSet
    transitive : ∀ {left middle right} →
      T.LessEqual order left middle →
      T.LessEqual order middle right →
      T.LessEqual order left right

    referenceIntegrand :
      Scale → Component → SlowField → Fine → Scalar

    suppression : Scale → Scalar

    pointwiseLargeFieldSuppression :
      ∀ (scale : Scale) (selectedComponent : Component)
        (slow : SlowField) (fine : Fine) →
      T.LessEqual order
        (Integral.selectedWith (T.sumData dataSet)
          (T.localIntegrand dataSet scale selectedComponent slow
            (T.oneFunctional dataSet)) slow fine)
        (Integral.selectedWith (T.sumData dataSet)
          (referenceIntegrand scale selectedComponent slow) slow fine)

    normalizedSuppressedReferenceFibre :
      ∀ (scale : Scale) (selectedComponent : Component)
        (slow : SlowField) →
      T.LessEqual order
        (Integral.foldSelected (T.sumData dataSet)
          (Integral.selectedWith (T.sumData dataSet)
            (referenceIntegrand scale selectedComponent slow) slow)
          slow
          (T.fastFibre dataSet scale selectedComponent))
        (suppression scale)

open TOperationPointwiseSuppressionData public

localTOperationBelowReferenceFibre :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (suppressionData : TOperationPointwiseSuppressionData dataSet)
    (scale : Scale)
    (selected : T.SecondClassComponent (T.classData dataSet) scale)
    (slow : SlowField) →
  T.LessEqual (order suppressionData)
    (T.localizedTOperation dataSet scale selected slow
      (T.oneFunctional dataSet))
    (Integral.foldSelected (T.sumData dataSet)
      (Integral.selectedWith (T.sumData dataSet)
        (referenceIntegrand suppressionData scale
          (T.component selected) slow) slow)
      slow
      (T.fastFibre dataSet scale (T.component selected)))
localTOperationBelowReferenceFibre {dataSet = dataSet}
  suppressionData scale selected slow =
  T.foldPointwiseMonotone
    (T.sumData dataSet)
    (T.LessEqual (order suppressionData))
    (T.reflexive (order suppressionData))
    (T.addMonotone (order suppressionData))
    (T.fastFibre dataSet scale (T.component selected))
    (Integral.selectedWith (T.sumData dataSet)
      (T.localIntegrand dataSet scale (T.component selected) slow
        (T.oneFunctional dataSet)) slow)
    (Integral.selectedWith (T.sumData dataSet)
      (referenceIntegrand suppressionData scale
        (T.component selected) slow) slow)
    slow
    (pointwiseLargeFieldSuppression suppressionData
      scale (T.component selected) slow)

tOperationSmallFactorFromPointwiseSuppression :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (suppressionData : TOperationPointwiseSuppressionData dataSet)
    (scale : Scale)
    (selected : T.SecondClassComponent (T.classData dataSet) scale)
    (slow : SlowField) →
  T.LessEqual (order suppressionData)
    (T.localizedTOperation dataSet scale selected slow
      (T.oneFunctional dataSet))
    (suppression suppressionData scale)
tOperationSmallFactorFromPointwiseSuppression suppressionData scale selected slow =
  transitive suppressionData
    (localTOperationBelowReferenceFibre suppressionData scale selected slow)
    (normalizedSuppressedReferenceFibre suppressionData
      scale (T.component selected) slow)

record Equation189Suppression
    (Scale Scalar : Set) : Set₁ where
  field
    one two beta0 : Scalar
    add divide multiply : Scalar → Scalar → Scalar
    expNegative : Scalar → Scalar
    p0 : Scale → Scalar
    suppression : Scale → Scalar
    suppressionDefinition : ∀ scale →
      suppression scale
      ≡ expNegative
          (multiply (divide two (add one beta0)) (p0 scale))

open Equation189Suppression public

record Equation189Reduction
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    pointwiseData : TOperationPointwiseSuppressionData dataSet
    equation189 : Equation189Suppression Scale Scalar
    suppressionAgrees : ∀ scale →
      suppression pointwiseData scale ≡ suppression equation189 scale

open Equation189Reduction public

tOperationEquation189FromPointwiseSuppression :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (reduction : Equation189Reduction dataSet)
    (scale : Scale)
    (selected : T.SecondClassComponent (T.classData dataSet) scale)
    (slow : SlowField) →
  T.LessEqual (order (pointwiseData reduction))
    (T.localizedTOperation dataSet scale selected slow
      (T.oneFunctional dataSet))
    (expNegative (equation189 reduction)
      (multiply (equation189 reduction)
        (divide (equation189 reduction)
          (two (equation189 reduction))
          (add (equation189 reduction)
            (one (equation189 reduction))
            (beta0 (equation189 reduction))))
        (p0 (equation189 reduction) scale)))
tOperationEquation189FromPointwiseSuppression {dataSet = dataSet} reduction scale selected slow =
  subst
    (λ upper → T.LessEqual (order (pointwiseData reduction))
      (T.localizedTOperation dataSet scale selected slow
        (T.oneFunctional dataSet))
      upper)
    (trans
      (suppressionAgrees reduction scale)
      (suppressionDefinition (equation189 reduction) scale))
    (tOperationSmallFactorFromPointwiseSuppression
      (pointwiseData reduction) scale selected slow)

finiteTOperationSuppressionSummationLevel : ProofLevel
finiteTOperationSuppressionSummationLevel = machineChecked

equation189ReductionAssemblyLevel : ProofLevel
equation189ReductionAssemblyLevel = machineChecked

equation189PointwiseWilsonSuppressionInputsLevel : ProofLevel
equation189PointwiseWilsonSuppressionInputsLevel = conditional

normalizedReferenceFastFibreInputsLevel : ProofLevel
normalizedReferenceFastFibreInputsLevel = conditional
