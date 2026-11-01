{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF1WilsonR295SameObjectWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact as R313
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo

------------------------------------------------------------------------
-- F1-B / LITERAL WILSON CYLINDER = SELECTED R295/T5 OBSERVABLE CARRIER
--
-- The frontier reconciliation initially left this as an opaque same-object
-- equality.  The older canonical-B archaeology is already sharper:
--
--   * R295 owns the exact finite-T5 expectation/source algebra;
--   * R313 machine-checks R295 -> R296 once the selected rational magnitude is
--     identified with ordinary absolute value;
--   * R315's PairwiseWilsonCylinderPresentation is parameterized by that SAME
--     PhysicalMeasureConvergenceData and TestObservable carrier;
--   * R315 requires explicit Wilson-product decoding and explicit equality of
--     Wilson multiplication with the T5 observable multiplication.
--
-- Therefore there is no additional theorem of the form
--
--     WilsonObservable ≡ R295Observable
--
-- to prove after these typed objects exist.  The remaining physical F1-B
-- payment is precisely an inhabitant of the R315 Wilson-cylinder presentation
-- on the R295-derived finite carrier.
------------------------------------------------------------------------

record PhysicalWilsonR295SameObjectWeld
    {Measure TestObservable PhysicalObservable Loop : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (r295 : R295.DirectT5StateFamilyJPresentation dataSet extension)
    (magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ∣ value ∣)
    (semantics :
      R310.PairwiseEuclideanTimeSemantics
        {PhysicalObservable = PhysicalObservable}
        {dataSet = dataSet}
        {extension = extension}
        {finite = R313.exactT5JMagnitudeFromR295 r295 magnitudeIsAbsolute})
    : Set₁ where
  field
    wilsonPresentation :
      R315.PairwiseWilsonCylinderPresentation {Loop = Loop} semantics

open PhysicalWilsonR295SameObjectWeld public

selectedPhysicalObservableIsWilsonProduct :
  ∀ {Measure TestObservable PhysicalObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {r295 : R295.DirectT5StateFamilyJPresentation dataSet extension}
    {magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ∣ value ∣}
    {semantics :
      R310.PairwiseEuclideanTimeSemantics
        {PhysicalObservable = PhysicalObservable}
        {dataSet = dataSet}
        {extension = extension}
        {finite = R313.exactT5JMagnitudeFromR295 r295 magnitudeIsAbsolute}}
    (weld : PhysicalWilsonR295SameObjectWeld
      {Loop = Loop} r295 magnitudeIsAbsolute semantics)
    observable →
  R310.decode semantics observable
  ≡ Thermo.productLoopObservable
      (R315.wilson (wilsonPresentation weld))
      (R315.leftLoops (wilsonPresentation weld) observable)
selectedPhysicalObservableIsWilsonProduct weld observable =
  R315.decodedIsWilsonProduct (wilsonPresentation weld) observable

wilsonMultiplicationIsExactT5Multiplication :
  ∀ {Measure TestObservable PhysicalObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {r295 : R295.DirectT5StateFamilyJPresentation dataSet extension}
    {magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ∣ value ∣}
    {semantics :
      R310.PairwiseEuclideanTimeSemantics
        {PhysicalObservable = PhysicalObservable}
        {dataSet = dataSet}
        {extension = extension}
        {finite = R313.exactT5JMagnitudeFromR295 r295 magnitudeIsAbsolute}}
    (weld : PhysicalWilsonR295SameObjectWeld
      {Loop = Loop} r295 magnitudeIsAbsolute semantics)
    left right →
  Thermo.multiplyObservable
      (R315.wilson (wilsonPresentation weld)) left right
  ≡ Gram.multiplyObservable (Gram.operations dataSet) left right
wilsonMultiplicationIsExactT5Multiplication weld left right =
  R315.wilsonMultiplyIsT5Multiply
    (wilsonPresentation weld) left right

------------------------------------------------------------------------
-- Frontier consequences.
------------------------------------------------------------------------

independentWilsonToR295CarrierEqualityRequired : Bool
independentWilsonToR295CarrierEqualityRequired = false

independentWilsonToR295CarrierEqualityRequiredIsFalse :
  independentWilsonToR295CarrierEqualityRequired ≡ false
independentWilsonToR295CarrierEqualityRequiredIsFalse = refl

r295ToR296CarrierCompilerOwned : Bool
r295ToR296CarrierCompilerOwned = true

r295ToR296CarrierCompilerOwnedIsTrue :
  r295ToR296CarrierCompilerOwned ≡ true
r295ToR296CarrierCompilerOwnedIsTrue = refl

wilsonT5OperationWeldCompilerOwnedOncePresentationExists : Bool
wilsonT5OperationWeldCompilerOwnedOncePresentationExists = true

wilsonT5OperationWeldCompilerOwnedOncePresentationExistsIsTrue :
  wilsonT5OperationWeldCompilerOwnedOncePresentationExists ≡ true
wilsonT5OperationWeldCompilerOwnedOncePresentationExistsIsTrue = refl

f1BPhysicalResidueIsR315Presentation : Bool
f1BPhysicalResidueIsR315Presentation = true

f1BPhysicalResidueIsR315PresentationIsTrue :
  f1BPhysicalResidueIsR315Presentation ≡ true
f1BPhysicalResidueIsR315PresentationIsTrue = refl

f1BSameObjectCompilerLevel : ProofLevel
f1BSameObjectCompilerLevel = machineChecked

f1BPhysicalWilsonPresentationLevel : ProofLevel
f1BPhysicalWilsonPresentationLevel = R315.round315SelectedWilsonPresentationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
