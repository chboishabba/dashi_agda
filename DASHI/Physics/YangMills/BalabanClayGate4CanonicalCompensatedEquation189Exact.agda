module DASHI.Physics.YangMills.BalabanClayGate4CanonicalCompensatedEquation189Exact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _≤_; _*_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Factors
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceNormalizationExact as Canonical
import DASHI.Physics.YangMills.BalabanClayGate4TCompensatedSixFactorBudgetExact as Compensated
import DASHI.Physics.YangMills.BalabanClayGate4Equation189PhysicalAssemblyExact as Equation189

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Target locator: equation (1.89), p. 387. The exact printed constant and full
-- primary hypotheses remain pending direct page verification. This module
-- closes the repository assembly: canonical positive reference normalization,
-- compensated six-factor pointwise budgeting and finite constrained integration
-- produce the localized T-operation small-factor theorem.
------------------------------------------------------------------------

record CanonicalCompensatedEquation189Data
    (Scale Fine SlowField Component Functional Traversal : Set)
    (tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ) : Set₁ where
  field
    canonicalReference :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData

    comparison : Compensated.CompensatedSixFactorComparison Scale Traversal

    order : T.FiniteTOperationOrderLaws tData
    orderTransitive : ∀ {left middle right} →
      T.LessEqual order left middle →
      T.LessEqual order middle right →
      T.LessEqual order left right
    rationalOrderImpliesTOperationOrder : ∀ {left right} →
      left ≤ right → T.LessEqual order left right

    traversalOf : Scale → Component → SlowField → Fine → Traversal

    oneIntegrandMeaning : ∀ (scale : Scale) (component : Component) (slow : SlowField) (fine : Fine) →
      T.localIntegrand tData scale component slow
        (T.oneFunctional tData) fine
      ≡ Factors.activity (Compensated.physical comparison) scale
          (traversalOf scale component slow fine)

    referenceIntegrandFactorMeaning : ∀ (scale : Scale) (component : Component) (slow : SlowField) (fine : Fine) →
      Canonical.referenceIntegrand canonicalReference
        scale component slow fine
      ≡ Compensated.residualSuppression comparison scale
        * Compensated.referenceProduct comparison
          scale (traversalOf scale component slow fine)

    suppressionConvention : ∀ (scale : Scale) →
      Canonical.suppression canonicalReference scale
      ≡ Compensated.residualSuppression comparison scale

open CanonicalCompensatedEquation189Data public

asCompensatedTPointwiseMeaning :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ} →
  (dataSet : CanonicalCompensatedEquation189Data
    Scale Fine SlowField Component Functional Traversal tData) →
  Compensated.CompensatedTPointwiseMeaning tData (comparison dataSet)
asCompensatedTPointwiseMeaning dataSet = record
  { order = order dataSet
  ; orderTransitive = orderTransitive dataSet
  ; rationalOrderImpliesTOperationOrder = rationalOrderImpliesTOperationOrder dataSet
  ; traversalOf = traversalOf dataSet
  ; oneIntegrandMeaning = oneIntegrandMeaning dataSet
  ; referenceNormalization =
      Canonical.canonicalPhysicalReferenceNormalization
        (canonicalReference dataSet)
  ; referenceIntegrandMeaning = referenceIntegrandFactorMeaning dataSet
  }

asPhysicalEquation189Data :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ} →
  CanonicalCompensatedEquation189Data
    Scale Fine SlowField Component Functional Traversal tData →
  Equation189.PhysicalEquation189Data tData
asPhysicalEquation189Data dataSet =
  Compensated.asPhysicalEquation189Data
    (asCompensatedTPointwiseMeaning dataSet)

canonicalTOperationSmallFactor :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    (dataSet : CanonicalCompensatedEquation189Data
      Scale Fine SlowField Component Functional Traversal tData)
    scale
    (selected : T.SecondClassComponent (T.classData tData) scale)
    slow →
  T.LessEqual (order dataSet)
    (T.localizedTOperation tData scale selected slow
      (T.oneFunctional tData))
    (Canonical.suppression (canonicalReference dataSet) scale)
canonicalTOperationSmallFactor dataSet =
  Equation189.physicalTOperationSmallFactor
    (asPhysicalEquation189Data dataSet)

canonicalTOperationSmallFactorInResidualConvention :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    (dataSet : CanonicalCompensatedEquation189Data
      Scale Fine SlowField Component Functional Traversal tData)
    scale
    (selected : T.SecondClassComponent (T.classData tData) scale)
    slow →
  T.LessEqual (order dataSet)
    (T.localizedTOperation tData scale selected slow
      (T.oneFunctional tData))
    (Compensated.residualSuppression (comparison dataSet) scale)
canonicalTOperationSmallFactorInResidualConvention dataSet scale selected slow =
  subst
    (λ upper → T.LessEqual (order dataSet)
      (T.localizedTOperation tData scale selected slow
        (T.oneFunctional tData)) upper)
    (suppressionConvention dataSet scale)
    (canonicalTOperationSmallFactor dataSet scale selected slow)

canonicalCompensatedPointwiseAssemblyLevel : ProofLevel
canonicalCompensatedPointwiseAssemblyLevel = machineChecked

canonicalEquation189DataAssemblyLevel : ProofLevel
canonicalEquation189DataAssemblyLevel = machineChecked

canonicalEquation189SmallFactorLevel : ProofLevel
canonicalEquation189SmallFactorLevel = machineChecked

physicalEquation189FactorMeaningInputsLevel : ProofLevel
physicalEquation189FactorMeaningInputsLevel = conditional

primaryEquation189PrintedConstantInputsLevel : ProofLevel
primaryEquation189PrintedConstantInputsLevel = conditional
