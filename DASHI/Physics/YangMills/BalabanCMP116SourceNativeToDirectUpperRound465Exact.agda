{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SourceNativeToDirectUpperRound465Exact where

------------------------------------------------------------------------
-- GOAL-1 Bgamma / ROUND465:
-- SOURCE-NATIVE Aq^d + t<=d -> TERMINAL R387 SELECTED UPPER.
--
-- R394 already compiles:
--   literal selected CMP116 response <= A q^(d_source)
--   t <= d_source.
--
-- R388/R389 already compile that to
--   literal selected response <= A q^t
-- once q^d is antitone.
--
-- The only remaining physical rate semantics are therefore:
--   * the chosen q lies in the decreasing regime;
--   * the reconstructed clustering envelope dominates A q^t.
--
-- This owner performs the final compiler step into R387.  It introduces no
-- CMP116 localization theorem, source-distance equality, or spectral estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectoryToSourceNativeRound394Exact as R394
import DASHI.Physics.YangMills.BalabanCMP116LiteralSourceNativeUpperRound389Exact as R389
import DASHI.Physics.YangMills.BalabanSourceNativeDistanceLowerRound388Exact as R388
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387

record SourceNativePhysicalRateSemantics
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (source :
      R342.LiteralTrajectoryCMP116Source
        base demands tests spectrumSource)
    (calibration : R394.SourceNativeEnvelopeCalibration source)
    : Set₁ where
  field
    ratioAntitone :
      R388.RationalPowerDistanceAntitone
        (R394.fastRatio calibration)

    geometricPhysicalTimeBelowSpectrumEnvelope :
      ∀ observable time →
      R394.fastAmplitude calibration
        ℚ.* Power.rationalPower (R394.fastRatio calibration) time
      ≤
      R281.clusteringEnvelope spectrumSource observable time

open SourceNativePhysicalRateSemantics public

selectedResponseBelowSpectrumEnvelope :
  ∀ {Measure TestObservable SpectralObservable Energy
      dataSet extension base demands tests spectrumSource source calibration}
    (semantics :
      SourceNativePhysicalRateSemantics
        {Measure = Measure} {TestObservable = TestObservable}
        {SpectralObservable = SpectralObservable} {Energy = Energy}
        {dataSet = dataSet} {extension = extension}
        {base = base} {demands = demands}
        {tests = tests} {spectrumSource = spectrumSource}
        source calibration) →
  ∀ cutoff observable time →
  let upper =
        R394.selectedSourceNativeUpper
          source calibration cutoff observable time
  in
  R389.selectedResponse upper
  ≤
  R281.clusteringEnvelope spectrumSource observable time
selectedResponseBelowSpectrumEnvelope
    {source = source} {calibration = calibration}
    semantics cutoff observable time =
  let
    upper =
      R394.selectedSourceNativeUpper
        source calibration cutoff observable time

    atTime =
      R389.literalSelectedResponseBelowPhysicalTimeGeometric
        upper
        (ratioAntitone semantics)
  in
  ℚP.≤-trans atTime
    (geometricPhysicalTimeBelowSpectrumEnvelope semantics observable time)

asDirectSelectedSpectralUpper :
  ∀ {Measure TestObservable SpectralObservable Energy
      dataSet extension base demands tests spectrumSource}
    (source :
      R342.LiteralTrajectoryCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {SpectralObservable = SpectralObservable} {Energy = Energy}
        {dataSet = dataSet} {extension = extension}
        base demands tests spectrumSource)
    (calibration : R394.SourceNativeEnvelopeCalibration source) →
  SourceNativePhysicalRateSemantics source calibration →
  R387.DirectSelectedSpectralUpper base tests spectrumSource
asDirectSelectedSpectralUpper source calibration semantics = record
  { R387.DirectSelectedSpectralUpper.selectedResponseBelowSpectrumEnvelope =
      λ cutoff observable time →
        selectedResponseBelowSpectrumEnvelope
          semantics cutoff observable time
  }

round465SourceNativeRateCompilerLevel : ProofLevel
round465SourceNativeRateCompilerLevel = machineChecked

round465PowerAntitoneAuthorityLevel : ProofLevel
round465PowerAntitoneAuthorityLevel =
  R388.round388RationalPowerDistanceAntitoneLevel

-- Bgamma is now decomposed into only:
--   (1) source-envelope -> Aq^d calibration,
--   (2) t <= d_source,
--   (3) Aq^t <= the selected physical clustering envelope.
-- R394/R388/R389/R465 compile everything else.
literalRound465SourceNativePhysicalRateSemanticsLevel : ProofLevel
literalRound465SourceNativePhysicalRateSemanticsLevel = conditional
