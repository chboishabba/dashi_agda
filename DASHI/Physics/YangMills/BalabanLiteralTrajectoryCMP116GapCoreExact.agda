{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTrajectoryCMP116GapCoreExact where

------------------------------------------------------------------------
-- LITERAL SELECTED-TRAJECTORY CMP116 -> POSITIVE TRANSFER GAP CORE
--
-- R342 states the published localization directly on the literal mode/time
-- selected mixed-J response and constructs the exact finite covariance upper.
-- No source-response equality, source-pair equality, or all-J-pairs theorem is
-- required at the terminal B consumer.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

literalTrajectoryCMP116BuildsPositiveTransferGapCore :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R342.LiteralTrajectoryCMP116Source
    base demands tests spectrumSource →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate
      (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
literalTrajectoryCMP116BuildsPositiveTransferGapCore
    {spectrumSource = spectrumSource} source positive =
  Gap.positiveTransferGapCoreFromModeTests
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (R342.literalTrajectorySourceBuildsSubgapUpper source)
    positive

literalTrajectoryCMP116GapCoreCompilerLevel : ProofLevel
literalTrajectoryCMP116GapCoreCompilerLevel = machineChecked

-- Remaining literal B theorem content:
--   * R342 literal selected differentiated localization;
--   * source envelope -> selected spectral envelope calibration;
--   * the same reconstructed spectrum's positive candidate / lower spectral
--     representation and slow-vs-fast contradiction.
literalTrajectoryCMP116LocalizationLevel : ProofLevel
literalTrajectoryCMP116LocalizationLevel =
  R342.round342LiteralSelectedLocalizationLevel

literalTrajectoryCMP116EnvelopeCalibrationLevel : ProofLevel
literalTrajectoryCMP116EnvelopeCalibrationLevel =
  R342.round342EnvelopeCalibrationLevel

literalTrajectoryCMP116SpectrumLevel : ProofLevel
literalTrajectoryCMP116SpectrumLevel =
  R281.round281PhysicalSpectralRepresentationAndRateInputsLevel
