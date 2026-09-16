{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedSourceNativeUpperRound397Exact where

------------------------------------------------------------------------
-- ROUND397 / ONE-SIDED SELECTED SOURCE-ENVELOPE ATTACHMENT
--
-- R396 required the selected source envelope to be EQUAL to the source-native
-- shell.  The R394 consumer only needs an upper bound.  Older CMP116/T5
-- application owners already expose exactly this weaker orientation:
--
--     sourceEnvelope <= selected rooted shell.
--
-- Therefore equality is an overpayment.  The least-privilege application is:
--
--     sourceEnvelope <= shellValue(d)
--     shellValue(d) <= A * q^d
--     time <= d.
--
-- This module performs only the transitive compiler step.  It introduces no
-- localization estimate and does not identify source and shell representations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectoryToSourceNativeRound394Exact as R394
import DASHI.Physics.YangMills.BalabanSourceNativeGeometricMajorantRound395Exact as R395

record SelectedSourceNativeUpperApplication
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (source : R342.LiteralTrajectoryCMP116Source
      base demands tests spectrumSource)
    (majorant : R395.SourceNativeGeometricMajorant) : Set₁ where
  field
    selectedSourceEnvelopeBelowMajorantShell :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
        distance = R342.sourceDistance source leftJ rightJ
      in
      R342.sourceEnvelope source cutoff
        (R342.sourceRoot source cutoff leftJ rightJ) distance
      ≤ R395.shellValue majorant distance

    selectedTimeBelowSourceDistance :
      ∀ observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      time Nat.≤ R342.sourceDistance source leftJ rightJ

open SelectedSourceNativeUpperApplication public

asR394Calibration :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    {source : R342.LiteralTrajectoryCMP116Source
      base demands tests spectrumSource}
    {majorant : R395.SourceNativeGeometricMajorant} →
  SelectedSourceNativeUpperApplication source majorant →
  R394.SourceNativeEnvelopeCalibration source
asR394Calibration
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    {source = source} {majorant = majorant} application = record
  { R394.SourceNativeEnvelopeCalibration.fastAmplitude =
      R395.amplitude majorant
  ; R394.SourceNativeEnvelopeCalibration.fastRatio =
      R395.ratio majorant
  ; R394.SourceNativeEnvelopeCalibration.fastAmplitudeNonnegative =
      R395.amplitudeNonnegative majorant
  ; R394.SourceNativeEnvelopeCalibration.sourceEnvelopeBelowSourceNativeGeometric =
      λ cutoff observable time →
        let
          index = R281.indexFor spectrumSource observable time
          left = R278.left tests index
          right = R278.right tests index
          leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
          rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
          distance = R342.sourceDistance source leftJ rightJ
        in
        ℚP.≤-trans
          (selectedSourceEnvelopeBelowMajorantShell application
            cutoff observable time)
          (R395.sourceNativeGeometricBound majorant distance)
  ; R394.SourceNativeEnvelopeCalibration.selectedTimeBelowSourceDistance =
      selectedTimeBelowSourceDistance application
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round397OneSidedAttachmentCompilerLevel : ProofLevel
round397OneSidedAttachmentCompilerLevel = machineChecked

selectedSourceEnvelopeShellEqualityRequired : Bool
selectedSourceEnvelopeShellEqualityRequired = false

selectedSourceEnvelopeShellEqualityRequiredIsFalse :
  selectedSourceEnvelopeShellEqualityRequired ≡ false
selectedSourceEnvelopeShellEqualityRequiredIsFalse = refl

selectedSourceEnvelopeUpperAttachmentStillProofBearing : Bool
selectedSourceEnvelopeUpperAttachmentStillProofBearing = true

selectedSourceEnvelopeUpperAttachmentStillProofBearingIsTrue :
  selectedSourceEnvelopeUpperAttachmentStillProofBearing ≡ true
selectedSourceEnvelopeUpperAttachmentStillProofBearingIsTrue = refl

sourceNativeGeometricMajorantStillProofBearing : Bool
sourceNativeGeometricMajorantStillProofBearing = true

sourceNativeGeometricMajorantStillProofBearingIsTrue :
  sourceNativeGeometricMajorantStillProofBearing ≡ true
sourceNativeGeometricMajorantStillProofBearingIsTrue = refl

oneSidedSourceDistanceStillProofBearing : Bool
oneSidedSourceDistanceStillProofBearing = true

oneSidedSourceDistanceStillProofBearingIsTrue :
  oneSidedSourceDistanceStillProofBearing ≡ true
oneSidedSourceDistanceStillProofBearingIsTrue = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
