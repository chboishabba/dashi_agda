{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralRateToGapRound482Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND482:
-- PUBLISHED LITERAL CMP116 + LOCAL ENERGY/RATE SEMANTICS -> POSITIVE GAP
--
-- R479 still exposed PositiveEnergy(gapCandidate) as an input because the
-- terminal compiler has that least-privilege ABI.  R301 already proves this
-- positivity from the actual local energy<->decay-rate semantics:
--
--   ratio(gapCandidate) = 1/2
--   0 <= 1/2 < 1
--       -> PositiveEnergy(gapCandidate).
--
-- Therefore the preferred B max-cut does NOT carry an arbitrary positive-gap
-- token.  It carries the physically meaningful local energy/rate semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact as R467
import DASHI.Physics.YangMills.BalabanLocalEnergyDecayRatioRound301Exact as R301
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralToGapRound479Exact as R479
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

publishedLiteralAndLocalRateBuildPositiveTransferGap :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R467.PublishedLiteralSelectedLocalization
    base tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = dataSet} →
  R301.LocalEnergyDecayRatioSemantics
    (R281.asReconstructedClusteringSpectrum spectrumSource) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
publishedLiteralAndLocalRateBuildPositiveTransferGap
    source limitClosure rateSemantics =
  R479.publishedLiteralSelectedBuildsPositiveTransferGap
    source
    limitClosure
    (R301.candidateGapPositiveFromLocalRate rateSemantics)

arbitraryPositiveCandidateGapTokenRequired : Bool
arbitraryPositiveCandidateGapTokenRequired = false

globalEnergyToDecayInverseRequired : Bool
globalEnergyToDecayInverseRequired = false

round482RateToGapCompilerLevel : ProofLevel
round482RateToGapCompilerLevel = machineChecked

literalRound482PublishedCMP116SourceLevel : ProofLevel
literalRound482PublishedCMP116SourceLevel =
  R467.literalRound467PublishedLiteralSelectedLocalizationLevel

literalRound482LocalEnergyRateSemanticsLevel : ProofLevel
literalRound482LocalEnergyRateSemanticsLevel =
  R301.round301PhysicalLocalEnergyRateSemanticsLevel
