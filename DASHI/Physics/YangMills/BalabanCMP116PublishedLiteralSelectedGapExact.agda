{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedGapExact where

------------------------------------------------------------------------
-- DIRECT-SOURCE H1 -> SAME SPECTRAL TRANSFER-GAP CORE.
--
-- R467 is the preferred Clay-facing H1 owner: the published CMP116 theorem is
-- already specialized directly to the literal selected mixed-log response on
-- one common analytic domain, followed by one physical envelope calibration.
--
-- The historical R455 adapter is typed through R454.  That is no longer
-- necessary.  R467 already constructs the exact R387.DirectSelectedSpectralUpper
-- consumed by the generic terminal gap compiler, so this module composes those
-- owners directly.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact as R467
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final

literalPublishedSelectedBuildsPositiveTransferGap :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable}
      {Energy = Energy}
      dataSet extension tests} →
  R467.PublishedLiteralSelectedLocalization
    base tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = dataSet} →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
literalPublishedSelectedBuildsPositiveTransferGap source limitClosure positive =
  Final.directSelectedUpperBuildsPositiveTransferGapCore
    (R467.asDirectSelectedSpectralUpper source)
    limitClosure
    positive

round467ToGapCompilerLevel : ProofLevel
round467ToGapCompilerLevel = machineChecked

-- No new physical payment is introduced here.  The physical H1 frontier
-- remains exactly R467's literal CMP116 application plus physical envelope
-- calibration; selected expectation/limit closure and same-H interpretation
-- belong to H2/H3.
literalPublishedSelectedAdditionalPhysicalPaymentLevel : ProofLevel
literalPublishedSelectedAdditionalPhysicalPaymentLevel = machineChecked
