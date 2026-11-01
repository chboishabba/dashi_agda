{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralToGapRound479Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND479:
-- PUBLISHED LITERAL SELECTED CMP116 -> TERMINAL POSITIVE TRANSFER GAP
--
-- R467 already states the source theorem directly on the literal selected
-- mixed-log response and compiles it to R387.DirectSelectedSpectralUpper.
-- Therefore the preferred B route can feed the terminal gap compiler directly;
-- the older R454/R455 compatibility package is not a mandatory intermediate.
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
import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

publishedLiteralSelectedBuildsPositiveTransferGap :
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
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
publishedLiteralSelectedBuildsPositiveTransferGap
    source limitClosure positiveGap =
  Final.directSelectedUpperBuildsPositiveTransferGapCore
    (R467.asDirectSelectedSpectralUpper source)
    limitClosure
    positiveGap

round479PublishedLiteralToGapCompilerLevel : ProofLevel
round479PublishedLiteralToGapCompilerLevel = machineChecked

olderR454R455CompatibilityRouteMandatory : Bool
olderR454R455CompatibilityRouteMandatory = false

postHocCMP116MagnitudeEqualityRequired : Bool
postHocCMP116MagnitudeEqualityRequired = false

cmp109PolarizationDetourRequired : Bool
cmp109PolarizationDetourRequired = false

literalRound479PublishedCMP116SourceLevel : ProofLevel
literalRound479PublishedCMP116SourceLevel =
  R467.literalRound467PublishedLiteralSelectedLocalizationLevel
