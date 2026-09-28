{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectoryToRound467Round579Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND579:
-- THE SOURCE-NATIVE R342 SELECTED CMP116 THEOREM INHABITS THE R467 ENDPOINT.
--
-- R342 already states the published differentiated-localization payment
-- directly on the literal selected mixed-log response and already carries the
-- physical source-envelope -> spectral-envelope calibration.
--
-- Therefore R467 needs no new analytic estimate, no abstract source magnitude,
-- and no post-hoc equality.  Its published common domain is simply the
-- canonical CMP116 common domain already used by R342.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact as R467

literalTrajectoryBuildsPublishedLiteralSelectedLocalization :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R342.LiteralTrajectoryCMP116Source base demands tests spectrumSource →
  R467.PublishedLiteralSelectedLocalization base tests spectrumSource
literalTrajectoryBuildsPublishedLiteralSelectedLocalization
    {base = base} {demands = demands} source = record
  { R467.PublishedLiteralSelectedLocalization.commonDomain =
      R114.canonicalCMP116CommonDomain
        {R318.Scale base} {R318.Volume base} demands
  ; R467.PublishedLiteralSelectedLocalization.sourceRoot =
      R342.sourceRoot source
  ; R467.PublishedLiteralSelectedLocalization.sourceDistance =
      R342.sourceDistance source
  ; R467.PublishedLiteralSelectedLocalization.sourceEnvelope =
      R342.sourceEnvelope source
  ; R467.PublishedLiteralSelectedLocalization.literalSelectedCMP116Localization =
      R342.literalSelectedDifferentiatedLocalization source
  ; R467.PublishedLiteralSelectedLocalization.sourceEnvelopeBelowPhysicalClusteringEnvelope =
      R342.sourceEnvelopeBelowSpectrumEnvelope source
  }

------------------------------------------------------------------------
-- Exact frontier after this compiler.
--
-- The R467 inhabitant itself is therefore not a stronger source theorem than
-- R342.  The physical H1 payment is exactly the two source-native R342 fields:
--
--   * literal selected differentiated localization on the common CMP116 domain;
--   * source-envelope -> selected physical spectral-envelope calibration.
--
-- The rational ordered-limit closure carried by R342 is downstream gap
-- machinery and is not required to construct R467.
------------------------------------------------------------------------

round579R342ToR467CompilerLevel : ProofLevel
round579R342ToR467CompilerLevel = machineChecked

round579LiteralSelectedCMP116ApplicationLevel : ProofLevel
round579LiteralSelectedCMP116ApplicationLevel =
  R342.round342LiteralSelectedLocalizationLevel

round579PhysicalResidualRateCalibrationLevel : ProofLevel
round579PhysicalResidualRateCalibrationLevel =
  R342.round342EnvelopeCalibrationLevel
