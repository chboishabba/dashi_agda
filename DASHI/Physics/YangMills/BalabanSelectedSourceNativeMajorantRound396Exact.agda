{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedSourceNativeMajorantRound396Exact where

------------------------------------------------------------------------
-- ROUND396 / SELECTED SOURCE ENVELOPE -> SOURCE-NATIVE GEOMETRIC MAJORANT
--
-- R395 owns the generic consumer-facing inequality
--
--     shellValue(d) <= A * q^d
--
-- without requiring q <= 1/2.  Therefore R394 does not need an independent
-- pointwise proof of `sourceEnvelope <= A*q^d` once the selected source envelope
-- is attached to that shell on the same selected distance.
--
-- The remaining application data are exactly:
--   * selected source-envelope = source-native shell at the SAME distance;
--   * time <= that source distance.
--
-- Everything else in the R394 calibration is projection/compiler work.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

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

record SelectedSourceNativeMajorantApplication
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
    selectedSourceEnvelopeIsMajorantShell :
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
      ≡ R395.shellValue majorant distance

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

open SelectedSourceNativeMajorantApplication public

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
  SelectedSourceNativeMajorantApplication source majorant →
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
        subst
          (λ shell →
            shell ≤ R395.amplitude majorant
              * DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact.rationalPower
                  (R395.ratio majorant) distance)
          (sym (selectedSourceEnvelopeIsMajorantShell application
            cutoff observable time))
          (R395.sourceNativeGeometricBound majorant distance)
  ; R394.SourceNativeEnvelopeCalibration.selectedTimeBelowSourceDistance =
      selectedTimeBelowSourceDistance application
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round396SelectedMajorantCompilerLevel : ProofLevel
round396SelectedMajorantCompilerLevel = machineChecked

pointwiseSourceGeometricBoundIndependentLeaf : Bool
pointwiseSourceGeometricBoundIndependentLeaf = false

pointwiseSourceGeometricBoundIndependentLeafIsFalse :
  pointwiseSourceGeometricBoundIndependentLeaf ≡ false
pointwiseSourceGeometricBoundIndependentLeafIsFalse = refl

selectedSourceEnvelopeShellAttachmentStillProofBearing : Bool
selectedSourceEnvelopeShellAttachmentStillProofBearing = true

selectedSourceEnvelopeShellAttachmentStillProofBearingIsTrue :
  selectedSourceEnvelopeShellAttachmentStillProofBearing ≡ true
selectedSourceEnvelopeShellAttachmentStillProofBearingIsTrue = refl

oneSidedSourceDistanceStillProofBearing : Bool
oneSidedSourceDistanceStillProofBearing = true

oneSidedSourceDistanceStillProofBearingIsTrue :
  oneSidedSourceDistanceStillProofBearing ≡ true
oneSidedSourceDistanceStillProofBearingIsTrue = refl

sourceNativeRatioIsNotDyadicByType : Bool
sourceNativeRatioIsNotDyadicByType = true

sourceNativeRatioIsNotDyadicByTypeIsTrue :
  sourceNativeRatioIsNotDyadicByType ≡ true
sourceNativeRatioIsNotDyadicByTypeIsTrue = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
