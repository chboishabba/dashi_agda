{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonP2ExpectationConvergenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.YMClayLiteralWilsonS2CanonicalProductPresentationExact as S2
import DASHI.Physics.YangMills.YMClayLiteralWilsonS2SameAlgebraBoundExact as S2Same

------------------------------------------------------------------------
-- ROUTE-S P2 / THREE LITERAL-WILSON EXPECTATION LIMITS
--
-- P2 was stated as three convergence hypotheses:
--
--   E_k[F G_t] -> E[F G_t]
--   E_k[F]     -> E[F]
--   E_k[G_t]   -> E[G_t].
--
-- On the existing T5 carrier these are not three independent analytic
-- theorems.  PhysicalMeasureConvergenceData already proves expectation
-- convergence for every BoundedObservable.  R315 proves boundedness of the
-- selected left, translated-right, and product observables from ONE literal
-- Wilson-cylinder presentation.
--
-- Therefore the actual P2 physical seam is only the same-carrier Wilson
-- presentation.  Once that presentation is supplied, all three limits below
-- are machine-constructed.
------------------------------------------------------------------------

record LiteralWilsonSelectedExpectationLimits
    {Measure TestObservable PhysicalObservable Loop : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (semantics : R310.PairwiseEuclideanTimeSemantics
      {PhysicalObservable = PhysicalObservable}
      {dataSet = dataSet} {extension = extension} {finite = finite})
    (left right : PhysicalObservable)
    (time : Nat)
    : Set₁ where
  field
    leftExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            (R310.decode semantics left))
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          (R310.decode semantics left))

    translatedRightExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            (R310.timeTranslate semantics right time))
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          (R310.timeTranslate semantics right time))

    productExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            (Gram.multiplyObservable (Gram.operations dataSet)
              (R310.decode semantics left)
              (R310.timeTranslate semantics right time)))
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          (Gram.multiplyObservable (Gram.operations dataSet)
            (R310.decode semantics left)
            (R310.timeTranslate semantics right time)))

open LiteralWilsonSelectedExpectationLimits public

literalWilsonSelectedExpectationLimits :
  ∀ {Measure TestObservable PhysicalObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (semantics : R310.PairwiseEuclideanTimeSemantics
      {PhysicalObservable = PhysicalObservable}
      {dataSet = dataSet} {extension = extension} {finite = finite}) →
  R315.PairwiseWilsonCylinderPresentation {Loop = Loop} semantics →
  (left right : PhysicalObservable) →
  (time : Nat) →
  LiteralWilsonSelectedExpectationLimits semantics left right time
literalWilsonSelectedExpectationLimits {dataSet = dataSet}
    semantics presentation left right time =
  let
    bounded = R315.asPairwiseBoundedTestAdmissibility semantics presentation
  in
  record
    { leftExpectationConverges =
        R278.selectedExpectationConverges dataSet
          (R310.decode semantics left)
          (R310.leftBounded bounded left)
    ; translatedRightExpectationConverges =
        R278.selectedExpectationConverges dataSet
          (R310.timeTranslate semantics right time)
          (R310.translatedRightBounded bounded right time)
    ; productExpectationConverges =
        R278.selectedExpectationConverges dataSet
          (Gram.multiplyObservable (Gram.operations dataSet)
            (R310.decode semantics left)
            (R310.timeTranslate semantics right time))
          (R310.translatedProductBounded bounded left right time)
    }


------------------------------------------------------------------------
-- Canonical S2 carrier -> all three P2 expectation limits.
------------------------------------------------------------------------

canonicalS2BuildsSelectedExpectationLimits :
  ∀ {Measure TestObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (inputs : S2.CanonicalWilsonProductS2Inputs finite)
    (left right : List Loop)
    (time : Nat) →
  LiteralWilsonSelectedExpectationLimits
    (S2.canonicalWilsonPairwiseSemantics inputs) left right time
canonicalS2BuildsSelectedExpectationLimits inputs left right time =
  literalWilsonSelectedExpectationLimits
    (S2.canonicalWilsonPairwiseSemantics inputs)
    (S2.canonicalWilsonCylinderPresentation inputs)
    left right time


sameAlgebraS2BuildsSelectedExpectationLimits :
  ∀ {Measure TestObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (inputs : S2Same.SameAlgebraCanonicalS2Inputs {Loop = Loop} finite)
    (left right : List Loop)
    (time : Nat) →
  LiteralWilsonSelectedExpectationLimits
    (S2.canonicalWilsonPairwiseSemantics
      (S2Same.asCanonicalWilsonProductS2Inputs inputs))
    left right time
sameAlgebraS2BuildsSelectedExpectationLimits inputs left right time =
  canonicalS2BuildsSelectedExpectationLimits
    (S2Same.asCanonicalWilsonProductS2Inputs inputs)
    left right time

------------------------------------------------------------------------
-- Frontier reduction.
------------------------------------------------------------------------

threeExpectationLimitsIndependentPhysicalLeaves : Bool
threeExpectationLimitsIndependentPhysicalLeaves = false

threeExpectationLimitsIndependentPhysicalLeavesIsFalse :
  threeExpectationLimitsIndependentPhysicalLeaves ≡ false
threeExpectationLimitsIndependentPhysicalLeavesIsFalse = refl

sameCarrierWilsonPresentationStillPhysical : Bool
sameCarrierWilsonPresentationStillPhysical = true

sameCarrierWilsonPresentationStillPhysicalIsTrue :
  sameCarrierWilsonPresentationStillPhysical ≡ true
sameCarrierWilsonPresentationStillPhysicalIsTrue = refl

p2ExpectationConvergenceCompilerLevel : ProofLevel
p2ExpectationConvergenceCompilerLevel = machineChecked

p2SameCarrierWilsonPresentationLevel : ProofLevel
p2SameCarrierWilsonPresentationLevel = R315.round315SelectedWilsonPresentationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
