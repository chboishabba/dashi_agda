{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact where

------------------------------------------------------------------------
-- ROUND315 / H2b FROM EXISTING FINITE WILSON-CYLINDER BOUNDS
--
-- R310 asks separately that the decoded left observable, translated right
-- observable, and their product are bounded on the exact T5 carrier.  The T5
-- thermodynamic owner already proves uniform bounds for every finite product of
-- Wilson-loop observables.  Therefore H2b should not store three unrelated
-- boundedness assumptions when the selected observables are presented by those
-- finite Wilson products.
--
-- Physical/application payments retained here:
--   * selected physical observables/time translates are the stated finite
--     Wilson-cylinder products;
--   * the existing Wilson `Bound` predicate entails the exact T5
--     `BoundedObservable` predicate on the same observable carrier.
--
-- Once those two semantics are supplied, all three R310 bounded-test receipts
-- are compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310

record PairwiseWilsonCylinderPresentation
    {Measure TestObservable PhysicalObservable Loop : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (semantics : R310.PairwiseEuclideanTimeSemantics
      {PhysicalObservable = PhysicalObservable}
      {dataSet = dataSet} {extension = extension} {finite = finite})
    : Set₁ where
  field
    wilson : Thermo.WilsonCylinderBoundData Loop TestObservable ℚ

    leftLoops : PhysicalObservable → List Loop
    translatedRightLoops : PhysicalObservable → Nat → List Loop

    decodedIsWilsonProduct : ∀ observable →
      R310.decode semantics observable
      ≡ Thermo.productLoopObservable wilson (leftLoops observable)

    translatedIsWilsonProduct : ∀ observable time →
      R310.timeTranslate semantics observable time
      ≡ Thermo.productLoopObservable wilson (translatedRightLoops observable time)

    -- Same-carrier admissibility meaning.  This is the only predicate weld:
    -- the quantitative Wilson bound already proved by the T5 owner certifies
    -- the exact bounded-test predicate used by the selected expectation lane.
    wilsonBoundImpliesT5Bounded : ∀ observable bound →
      Thermo.Bound wilson observable bound →
      Gram.BoundedObservable dataSet observable

open PairwiseWilsonCylinderPresentation public

wilsonProductIsT5Bounded :
  ∀ {Measure TestObservable PhysicalObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {semantics : R310.PairwiseEuclideanTimeSemantics
      {PhysicalObservable = PhysicalObservable}
      {dataSet = dataSet} {extension = extension} {finite = finite}}
    (presentation : PairwiseWilsonCylinderPresentation
      {Loop = Loop} semantics)
    loops →
  Gram.BoundedObservable dataSet
    (Thermo.productLoopObservable (wilson presentation) loops)
wilsonProductIsT5Bounded presentation loops =
  wilsonBoundImpliesT5Bounded presentation
    (Thermo.productLoopObservable (wilson presentation) loops)
    (Thermo.productLoopBound (wilson presentation) loops)
    (Thermo.finiteProductWilsonObservableUniformBound
      (wilson presentation) loops)

asPairwiseBoundedTestAdmissibility :
  ∀ {Measure TestObservable PhysicalObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (semantics : R310.PairwiseEuclideanTimeSemantics
      {PhysicalObservable = PhysicalObservable}
      {dataSet = dataSet} {extension = extension} {finite = finite}) →
  PairwiseWilsonCylinderPresentation {Loop = Loop} semantics →
  R310.PairwiseBoundedTestAdmissibility semantics
asPairwiseBoundedTestAdmissibility {dataSet = dataSet}
    semantics presentation = record
  { R310.PairwiseBoundedTestAdmissibility.leftBounded = λ observable →
      subst (Gram.BoundedObservable dataSet)
        (symEq (decodedIsWilsonProduct presentation observable))
        (wilsonProductIsT5Bounded presentation
          (leftLoops presentation observable))
  ; R310.PairwiseBoundedTestAdmissibility.translatedRightBounded =
      λ observable time →
        subst (Gram.BoundedObservable dataSet)
          (symEq (translatedIsWilsonProduct presentation observable time))
          (wilsonProductIsT5Bounded presentation
            (translatedRightLoops presentation observable time))
  ; R310.PairwiseBoundedTestAdmissibility.translatedProductBounded =
      λ left right time →
        let
          leftObservable = R310.decode semantics left
          rightObservable = R310.timeTranslate semantics right time
          leftBound =
            subst (Gram.BoundedObservable dataSet)
              (symEq (decodedIsWilsonProduct presentation left))
              (wilsonProductIsT5Bounded presentation
                (leftLoops presentation left))
          rightBound =
            subst (Gram.BoundedObservable dataSet)
              (symEq (translatedIsWilsonProduct presentation right time))
              (wilsonProductIsT5Bounded presentation
                (translatedRightLoops presentation right time))
          leftWilsonBound =
            Thermo.finiteProductWilsonObservableUniformBound
              (wilson presentation) (leftLoops presentation left)
          rightWilsonBound =
            Thermo.finiteProductWilsonObservableUniformBound
              (wilson presentation) (translatedRightLoops presentation right time)
          productWilsonBound =
            Thermo.multiplyBound (wilson presentation)
              (Thermo.productLoopObservable (wilson presentation)
                (leftLoops presentation left))
              (Thermo.productLoopObservable (wilson presentation)
                (translatedRightLoops presentation right time))
              (Thermo.productLoopBound (wilson presentation)
                (leftLoops presentation left))
              (Thermo.productLoopBound (wilson presentation)
                (translatedRightLoops presentation right time))
              leftWilsonBound rightWilsonBound
          productBounded =
            wilsonBoundImpliesT5Bounded presentation
              (Thermo.multiplyObservable (wilson presentation)
                (Thermo.productLoopObservable (wilson presentation)
                  (leftLoops presentation left))
                (Thermo.productLoopObservable (wilson presentation)
                  (translatedRightLoops presentation right time)))
              (Thermo.multiplyScalar (wilson presentation)
                (Thermo.productLoopBound (wilson presentation)
                  (leftLoops presentation left))
                (Thermo.productLoopBound (wilson presentation)
                  (translatedRightLoops presentation right time)))
              productWilsonBound
          productEquality :
            Gram.multiplyObservable (Gram.operations dataSet)
              leftObservable rightObservable
            ≡ Thermo.multiplyObservable (wilson presentation)
                (Thermo.productLoopObservable (wilson presentation)
                  (leftLoops presentation left))
                (Thermo.productLoopObservable (wilson presentation)
                  (translatedRightLoops presentation right time))
          productEquality
            rewrite decodedIsWilsonProduct presentation left
                  | translatedIsWilsonProduct presentation right time = refl
        in
        subst (Gram.BoundedObservable dataSet)
          (symEq productEquality) productBounded
  }
  where
    symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symEq refl = refl

record Round315Boundary : Set where
  constructor round315-boundary
  field
    threeIndependentBoundedTestLeavesRequired : Bool
    threeIndependentBoundedTestLeavesRequiredIsFalse :
      threeIndependentBoundedTestLeavesRequired ≡ false
    finiteWilsonCylinderBoundTheoremReused : Bool
    finiteWilsonCylinderBoundTheoremReusedIsTrue :
      finiteWilsonCylinderBoundTheoremReused ≡ true
    selectedObservableWilsonPresentationStillPhysical : Bool
    selectedObservableWilsonPresentationStillPhysicalIsTrue :
      selectedObservableWilsonPresentationStillPhysical ≡ true
    boundPredicateSameCarrierMeaningStillRequired : Bool
    boundPredicateSameCarrierMeaningStillRequiredIsTrue :
      boundPredicateSameCarrierMeaningStillRequired ≡ true

canonicalRound315Boundary : Round315Boundary
canonicalRound315Boundary =
  round315-boundary false refl true refl true refl true refl

round315BoundedTestCompilerLevel : ProofLevel
round315BoundedTestCompilerLevel = machineChecked

round315WilsonCylinderUniformBoundLevel : ProofLevel
round315WilsonCylinderUniformBoundLevel = standardImported

round315SelectedWilsonPresentationLevel : ProofLevel
round315SelectedWilsonPresentationLevel = conditional
