{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedTwoSourceGapRound455Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND455
-- SELECTED CMP116 LOCALIZATION -> POSITIVE TRANSFER GAP.
--
-- R454 is the human-proof finite theorem:
--
--   published CMP116 localization
--   + common-domain applicability
--   + literal mixed-log same-object identification
--   + one-sided physical envelope calibration
--     => exact finite selected covariance clustering upper.
--
-- The existing R387/R342/Gap terminal chain then carries that finite theorem
-- through the same continuum covariance and the already-owned spectral argument.
-- This module is only the final composition; it introduces no estimate.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116SelectedTwoSourceLocalizationRound454Exact as R454
import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

selectedTwoSourceLocalizationBuildsPositiveTransferGap :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R454.SelectedTwoSourceLocalization
    base demands source tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = dataSet} →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
selectedTwoSourceLocalizationBuildsPositiveTransferGap
    selected limitClosure positiveGap =
  Final.directSelectedUpperBuildsPositiveTransferGapCore
    (R454.directSelectedSpectralUpper selected)
    limitClosure
    positiveGap

round455FiniteToContinuumGapCompilerLevel : ProofLevel
round455FiniteToContinuumGapCompilerLevel = machineChecked

-- No additional B mathematics is introduced here.
-- The Goal-1 B source/application frontier is exactly R454's Bα/Bβ/Bγ package.
literalRound455AdditionalPhysicalPaymentLevel : ProofLevel
literalRound455AdditionalPhysicalPaymentLevel = machineChecked
