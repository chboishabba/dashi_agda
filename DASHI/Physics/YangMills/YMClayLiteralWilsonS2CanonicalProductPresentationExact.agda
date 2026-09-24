{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonS2CanonicalProductPresentationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; map)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315

------------------------------------------------------------------------
-- ROUTE-S S2 / CANONICAL FINITE-WILSON-PRODUCT PHYSICAL CARRIER
--
-- R315 is intentionally generic and therefore stores four representation
-- coordinates:
--
--   leftLoops
--   translatedRightLoops
--   decodedIsWilsonProduct
--   translatedIsWilsonProduct.
--
-- For the literal Wilson route this is unnecessary.  Choose the physical
-- observable carrier itself to be List Loop, decode a list by the canonical
-- finite Wilson product, and translate it by mapping the loop translation.
-- Both representation equalities are then definitional.
--
-- The remaining physical inputs are exactly:
--
--   * the Euclidean loop translation;
--   * support distance = Euclidean time for the selected pair;
--   * equality of the Wilson multiplication with the T5 multiplication;
--   * the Wilson-bound -> T5-BoundedObservable interpretation.
------------------------------------------------------------------------

record CanonicalWilsonProductS2Inputs
    {Measure TestObservable Loop : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (finite : R296.ExactT5JMagnitudePresentation dataSet extension)
    : Set₁ where
  field
    wilson : Thermo.WilsonCylinderBoundData Loop TestObservable ℚ

    translateLoop : Loop → Nat → Loop

    supportDistanceIsTime : ∀ left right time →
      R304.physicalDistance (R296.asDirectT5TwoSourceShell finite)
        (Thermo.productLoopObservable wilson left)
        (Thermo.productLoopObservable wilson
          (map (λ loop → translateLoop loop time) right))
      ≡ time

    wilsonMultiplyIsT5Multiply : ∀ left right →
      Thermo.multiplyObservable wilson left right
      ≡ Gram.multiplyObservable (Gram.operations dataSet) left right

    wilsonBoundImpliesT5Bounded : ∀ observable bound →
      Thermo.Bound wilson observable bound →
      Gram.BoundedObservable dataSet observable

open CanonicalWilsonProductS2Inputs public

canonicalWilsonPairwiseSemantics :
  ∀ {Measure TestObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension} →
  CanonicalWilsonProductS2Inputs finite →
  R310.PairwiseEuclideanTimeSemantics
    {PhysicalObservable = List Loop}
    {dataSet = dataSet} {extension = extension} {finite = finite}
canonicalWilsonPairwiseSemantics inputs = record
  { R310.PairwiseEuclideanTimeSemantics.decode =
      Thermo.productLoopObservable (wilson inputs)
  ; R310.PairwiseEuclideanTimeSemantics.timeTranslate =
      λ loops time →
        Thermo.productLoopObservable (wilson inputs)
          (map (λ loop → translateLoop inputs loop time) loops)
  ; R310.PairwiseEuclideanTimeSemantics.supportDistanceIsTime =
      supportDistanceIsTime inputs
  }

canonicalWilsonCylinderPresentation :
  ∀ {Measure TestObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (inputs : CanonicalWilsonProductS2Inputs finite) →
  R315.PairwiseWilsonCylinderPresentation {Loop = Loop}
    (canonicalWilsonPairwiseSemantics inputs)
canonicalWilsonCylinderPresentation inputs = record
  { R315.PairwiseWilsonCylinderPresentation.wilson = wilson inputs
  ; R315.PairwiseWilsonCylinderPresentation.leftLoops = λ loops → loops
  ; R315.PairwiseWilsonCylinderPresentation.translatedRightLoops =
      λ loops time → map (λ loop → translateLoop inputs loop time) loops
  ; R315.PairwiseWilsonCylinderPresentation.decodedIsWilsonProduct =
      λ loops → refl
  ; R315.PairwiseWilsonCylinderPresentation.translatedIsWilsonProduct =
      λ loops time → refl
  ; R315.PairwiseWilsonCylinderPresentation.wilsonMultiplyIsT5Multiply =
      wilsonMultiplyIsT5Multiply inputs
  ; R315.PairwiseWilsonCylinderPresentation.wilsonBoundImpliesT5Bounded =
      wilsonBoundImpliesT5Bounded inputs
  }

canonicalWilsonBoundedTests :
  ∀ {Measure TestObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (inputs : CanonicalWilsonProductS2Inputs finite) →
  R310.PairwiseBoundedTestAdmissibility
    (canonicalWilsonPairwiseSemantics inputs)
canonicalWilsonBoundedTests inputs =
  R315.asPairwiseBoundedTestAdmissibility
    (canonicalWilsonPairwiseSemantics inputs)
    (canonicalWilsonCylinderPresentation inputs)

------------------------------------------------------------------------
-- Frontier reduction.
------------------------------------------------------------------------

independentDecodeToWilsonProductEqualityRequired : Bool
independentDecodeToWilsonProductEqualityRequired = false

independentDecodeToWilsonProductEqualityRequiredIsFalse :
  independentDecodeToWilsonProductEqualityRequired ≡ false
independentDecodeToWilsonProductEqualityRequiredIsFalse = refl

independentTranslatedWilsonProductEqualityRequired : Bool
independentTranslatedWilsonProductEqualityRequired = false

independentTranslatedWilsonProductEqualityRequiredIsFalse :
  independentTranslatedWilsonProductEqualityRequired ≡ false
independentTranslatedWilsonProductEqualityRequiredIsFalse = refl

canonicalFiniteWilsonListCarrierPaysRepresentation : Bool
canonicalFiniteWilsonListCarrierPaysRepresentation = true

canonicalFiniteWilsonListCarrierPaysRepresentationIsTrue :
  canonicalFiniteWilsonListCarrierPaysRepresentation ≡ true
canonicalFiniteWilsonListCarrierPaysRepresentationIsTrue = refl

supportDistanceTimeStillPhysical : Bool
supportDistanceTimeStillPhysical = true

supportDistanceTimeStillPhysicalIsTrue :
  supportDistanceTimeStillPhysical ≡ true
supportDistanceTimeStillPhysicalIsTrue = refl

wilsonT5MultiplicationWeldStillPhysical : Bool
wilsonT5MultiplicationWeldStillPhysical = true

wilsonT5MultiplicationWeldStillPhysicalIsTrue :
  wilsonT5MultiplicationWeldStillPhysical ≡ true
wilsonT5MultiplicationWeldStillPhysicalIsTrue = refl

wilsonBoundPredicateWeldStillPhysical : Bool
wilsonBoundPredicateWeldStillPhysical = true

wilsonBoundPredicateWeldStillPhysicalIsTrue :
  wilsonBoundPredicateWeldStillPhysical ≡ true
wilsonBoundPredicateWeldStillPhysicalIsTrue = refl

s2CanonicalProductPresentationCompilerLevel : ProofLevel
s2CanonicalProductPresentationCompilerLevel = machineChecked

s2RemainingPhysicalInputsLevel : ProofLevel
s2RemainingPhysicalInputsLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
