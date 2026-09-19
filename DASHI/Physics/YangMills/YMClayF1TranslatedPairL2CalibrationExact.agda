{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF1TranslatedPairL2CalibrationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.YMClayR295MarkedSourceAdapterExact as Adapter
import DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerExact as Dense
import DASHI.Physics.YangMills.YMClayF1WilsonR295SameObjectWeldExact as Wilson

------------------------------------------------------------------------
-- F1-C / TRANSLATED TWO-SLICE ROOTED-SHELL -> PHYSICAL L2 CALIBRATION
--
-- After the R315 same-object presentation, the selected source pair required
-- by the transfer criterion is:
--
--     decode(psi), timeTranslate(psi,1)
--
-- not decode(psi),decode(psi).
--
-- The least-privilege quantitative payment is only
--
--     rootedShell_k(decode psi, tau_1 psi)
--       <= c_k * normSq_k(psi).
--
-- No equality of envelopes is required.  No new marked-source/covariance
-- compiler is required.  This owner compiles exactly that one-sided physical
-- estimate into the corrected DenseMarkedSourceF1Weld.
------------------------------------------------------------------------

oneStep : Nat
oneStep = suc zero

record TranslatedPairPhysicalL2Calibration
    {Measure TestObservable PhysicalObservable Loop : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (r295 : R295.DirectT5StateFamilyJPresentation dataSet extension)
    (magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ℚ.∣ value ∣)
    (semantics :
      R310.PairwiseEuclideanTimeSemantics
        {PhysicalObservable = PhysicalObservable}
        {dataSet = dataSet}
        {extension = extension}
        {finite =
          DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact.exactT5JMagnitudeFromR295
            r295 magnitudeIsAbsolute})
    (wilsonWeld :
      Wilson.PhysicalWilsonR295SameObjectWeld
        {Loop = Loop} r295 magnitudeIsAbsolute semantics)
    : Set₁ where
  field
    DenseInPhysicalVacuumComplement : Set
    denseInPhysicalVacuumComplement : DenseInPhysicalVacuumComplement

    physicalNormSq :
      Nat → PhysicalObservable → ℚ

    decorrelationConstant :
      Nat → ℚ

    selectedOneStepEnvelopeBelowCKNormSq :
      ∀ psi cutoff →
      Shell.rootedShell
        (R295.shellData r295)
        (R295.scaleOf r295 cutoff)
        (R295.volumeOf r295 cutoff)
        (R295.connectingRoot r295 cutoff
          (R310.decode semantics psi)
          (R310.timeTranslate semantics psi oneStep))
        (R295.physicalDistance r295
          (R310.decode semantics psi)
          (R310.timeTranslate semantics psi oneStep))
      ≤ decorrelationConstant cutoff * physicalNormSq cutoff psi

open TranslatedPairPhysicalL2Calibration public

asDenseMarkedSourceF1Weld :
  ∀ {Measure TestObservable PhysicalObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {r295 : R295.DirectT5StateFamilyJPresentation dataSet extension}
    {magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ℚ.∣ value ∣}
    {semantics :
      R310.PairwiseEuclideanTimeSemantics
        {PhysicalObservable = PhysicalObservable}
        {dataSet = dataSet}
        {extension = extension}
        {finite =
          DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact.exactT5JMagnitudeFromR295
            r295 magnitudeIsAbsolute}}
    {wilsonWeld :
      Wilson.PhysicalWilsonR295SameObjectWeld
        {Loop = Loop} r295 magnitudeIsAbsolute semantics} →
  TranslatedPairPhysicalL2Calibration
    r295 magnitudeIsAbsolute semantics wilsonWeld →
  Dense.DenseMarkedSourceF1Weld
    (Adapter.r295MarkedResponse dataSet extension r295)
    (Adapter.r295MarkedSeparationDecayProducer dataSet extension r295)
asDenseMarkedSourceF1Weld
    {r295 = r295} {semantics = semantics} calibration = record
  { Dense.DenseMarkedSourceF1Weld.DensePhysicalObservable =
      _
  ; Dense.DenseMarkedSourceF1Weld.leftMarkedObservable =
      R310.decode semantics
  ; Dense.DenseMarkedSourceF1Weld.rightMarkedObservable =
      λ psi → R310.timeTranslate semantics psi oneStep
  ; Dense.DenseMarkedSourceF1Weld.DenseInPhysicalVacuumComplement =
      DenseInPhysicalVacuumComplement calibration
  ; Dense.DenseMarkedSourceF1Weld.denseInPhysicalVacuumComplement =
      denseInPhysicalVacuumComplement calibration
  ; Dense.DenseMarkedSourceF1Weld.SameLiteralWilsonTwoSliceObservables =
      _
  ; Dense.DenseMarkedSourceF1Weld.sameLiteralWilsonTwoSliceObservables =
      Wilson.wilsonPresentation _
  ; Dense.DenseMarkedSourceF1Weld.f1TargetBound =
      λ psi cutoff →
        decorrelationConstant calibration cutoff
          * physicalNormSq calibration cutoff psi
  ; Dense.DenseMarkedSourceF1Weld.lessEqualTransitive =
      λ lowerToMiddle middleToUpper cutoff →
        ℚP.≤-trans (lowerToMiddle cutoff) (middleToUpper cutoff)
  ; Dense.DenseMarkedSourceF1Weld.sourceEnvelopeBelowPhysicalF1Target =
      selectedOneStepEnvelopeBelowCKNormSq calibration
  }

independentEnvelopeEqualityRequired : Bool
independentEnvelopeEqualityRequired = false

independentEnvelopeEqualityRequiredIsFalse :
  independentEnvelopeEqualityRequired ≡ false
independentEnvelopeEqualityRequiredIsFalse = refl

diagonalSameObservablePairSuffices : Bool
diagonalSameObservablePairSuffices = false

diagonalSameObservablePairSufficesIsFalse :
  diagonalSameObservablePairSuffices ≡ false
diagonalSameObservablePairSufficesIsFalse = refl

translatedOneStepPairIsCanonical : Bool
translatedOneStepPairIsCanonical = true

translatedOneStepPairIsCanonicalIsTrue :
  translatedOneStepPairIsCanonical ≡ true
translatedOneStepPairIsCanonicalIsTrue = refl

remainingF1CIsOneSidedPhysicalContraction : Bool
remainingF1CIsOneSidedPhysicalContraction = true

remainingF1CIsOneSidedPhysicalContractionIsTrue :
  remainingF1CIsOneSidedPhysicalContraction ≡ true
remainingF1CIsOneSidedPhysicalContractionIsTrue = refl

physicalTranslatedPairL2CalibrationLevel : ProofLevel
physicalTranslatedPairL2CalibrationLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
