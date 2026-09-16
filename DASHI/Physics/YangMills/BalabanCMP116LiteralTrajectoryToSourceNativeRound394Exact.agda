{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectoryToSourceNativeRound394Exact where

------------------------------------------------------------------------
-- ROUND394 / R342 LITERAL TRAJECTORY -> R389 SOURCE-NATIVE UPPER
--
-- R342 already removes the post-hoc source-magnitude equality by stating the
-- CMP116 differentiated localization theorem directly on the literal selected
-- mixed-J response.  R389 gives the least-privilege scalar consumer shape:
--
--   selectedResponse <= A_fast * q_fast^(sourceDistance)
--   time <= sourceDistance.
--
-- The only bridge needed between those owners is therefore quantitative
-- calibration of the source envelope itself to a source-native `(A_fast,q_fast)`
-- geometric majorant, plus the one-sided source-distance geometry.  This module
-- performs that compiler step.  It does not re-prove CMP116 localization and it
-- does not reinstate any source-magnitude/root/distance equality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116LiteralSourceNativeUpperRound389Exact as R389

record SourceNativeEnvelopeCalibration
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
      base demands tests spectrumSource) : Set₁ where
  field
    fastAmplitude fastRatio : ℚ
    fastAmplitudeNonnegative : 0ℚ ≤ fastAmplitude

    -- Quantitative source-native reading of the already-owned exponential
    -- source envelope.  No selected response appears on the left here: R342's
    -- literal localization theorem supplies that preceding inequality.
    sourceEnvelopeBelowSourceNativeGeometric :
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
      ≤ fastAmplitude * Power.rationalPower fastRatio distance

    -- Least-privilege geometry required by R388/R389.
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

open SourceNativeEnvelopeCalibration public

selectedSourceNativeUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (source : R342.LiteralTrajectoryCMP116Source
      base demands tests spectrumSource) →
  SourceNativeEnvelopeCalibration source →
  ∀ cutoff observable time →
  R389.LiteralSelectedCMP116SourceNativeUpper
selectedSourceNativeUpper
    {dataSet = dataSet} {extension = extension} {base = base}
    {demands = demands} {tests = tests} {spectrumSource = spectrumSource}
    source calibration cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
    distance = R342.sourceDistance source leftJ rightJ

    commonInside =
      Common.sourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)

    literalBound =
      R342.literalSelectedDifferentiatedLocalization source
        cutoff observable time commonInside

    sourceNativeBound =
      sourceEnvelopeBelowSourceNativeGeometric calibration
        cutoff observable time

    selectedBelowSourceNative =
      ℚP.≤-trans literalBound sourceNativeBound
  in
  record
    { R389.LiteralSelectedCMP116SourceNativeUpper.selectedResponse =
        R278.magnitude extension
          (Cumulant.literalMixedSecondLogDerivative
            (R318.meaning base) leftJ rightJ cutoff)
    ; R389.LiteralSelectedCMP116SourceNativeUpper.fastAmplitude =
        fastAmplitude calibration
    ; R389.LiteralSelectedCMP116SourceNativeUpper.fastRatio =
        fastRatio calibration
    ; R389.LiteralSelectedCMP116SourceNativeUpper.sourceDistance = distance
    ; R389.LiteralSelectedCMP116SourceNativeUpper.time = time
    ; R389.LiteralSelectedCMP116SourceNativeUpper.fastAmplitudeNonnegative =
        fastAmplitudeNonnegative calibration
    ; R389.LiteralSelectedCMP116SourceNativeUpper.literalSelectedLocalization =
        selectedBelowSourceNative
    ; R389.LiteralSelectedCMP116SourceNativeUpper.selectedTimeBelowSourceDistance =
        selectedTimeBelowSourceDistance calibration observable time
    }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round394LiteralTrajectoryToSourceNativeCompilerLevel : ProofLevel
round394LiteralTrajectoryToSourceNativeCompilerLevel = machineChecked

r342LiteralLocalizationReused : Bool
r342LiteralLocalizationReused = true

r342LiteralLocalizationReusedIsTrue :
  r342LiteralLocalizationReused ≡ true
r342LiteralLocalizationReusedIsTrue = refl

postHocMagnitudeEqualityReintroduced : Bool
postHocMagnitudeEqualityReintroduced = false

postHocMagnitudeEqualityReintroducedIsFalse :
  postHocMagnitudeEqualityReintroduced ≡ false
postHocMagnitudeEqualityReintroducedIsFalse = refl

sourceNativeEnvelopeCalibrationStillProofBearing : Bool
sourceNativeEnvelopeCalibrationStillProofBearing = true

sourceNativeEnvelopeCalibrationStillProofBearingIsTrue :
  sourceNativeEnvelopeCalibrationStillProofBearing ≡ true
sourceNativeEnvelopeCalibrationStillProofBearingIsTrue = refl

oneSidedSourceDistanceStillProofBearing : Bool
oneSidedSourceDistanceStillProofBearing = true

oneSidedSourceDistanceStillProofBearingIsTrue :
  oneSidedSourceDistanceStillProofBearing ≡ true
oneSidedSourceDistanceStillProofBearingIsTrue = refl

literalSelectedLocalizationIndependentLeafAfterR342 : Bool
literalSelectedLocalizationIndependentLeafAfterR342 = false

literalSelectedLocalizationIndependentLeafAfterR342IsFalse :
  literalSelectedLocalizationIndependentLeafAfterR342 ≡ false
literalSelectedLocalizationIndependentLeafAfterR342IsFalse = refl

sourceNativeEnvelopeCalibrationLevel : ProofLevel
sourceNativeEnvelopeCalibrationLevel = conditional

selectedSourceDistanceLowerLevel : ProofLevel
selectedSourceDistanceLowerLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
