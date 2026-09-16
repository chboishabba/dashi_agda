{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact where

------------------------------------------------------------------------
-- ROUND387 / DIRECT SELECTED SPECTRAL UPPER
--
-- R343 already weakened the historical source-response equality to the
-- one-sided inequality actually used by the mass-gap consumer:
--
--   selected mixed-log response <= source envelope
--   source envelope              <= spectral clustering envelope.
--
-- The terminal consumer never inspects the intermediate source envelope,
-- source root, source distance, or their semantic provenance.  Those remain
-- valuable producer-side/source-native coordinates, but they are not fields of
-- the least-privilege terminal ABI.
--
-- The direct YM theorem is therefore only
--
--   |D^2_{J_L,J_R} log Z_N| <= clusteringEnvelope(O,t)
--
-- on the exact mode/time-selected pair.  Standard one-sided closure under the
-- already-owned R278 finite->continuum convergence stays a separate analysis
-- authority.  This owner adds no decay estimate; R343 mechanically compiles to
-- it, while the converse intentionally cannot recover source-envelope data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116R281SelectedSourceUpperRound343Exact as R343

------------------------------------------------------------------------
-- Least-privilege terminal producer.
------------------------------------------------------------------------

record DirectSelectedSpectralUpper
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests)
    : Set₁ where
  field
    selectedResponseBelowSpectrumEnvelope :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
          leftJ rightJ cutoff)
      ≤ R281.clusteringEnvelope spectrumSource observable time

open DirectSelectedSpectralUpper public

------------------------------------------------------------------------
-- Stronger historical/source-native R343 producer -> R387.
------------------------------------------------------------------------

fromR343 :
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
  R343.SelectedResponseSourceUpperApplication
    base demands source tests spectrumSource →
  DirectSelectedSpectralUpper base tests spectrumSource
fromR343 application = record
  { selectedResponseBelowSpectrumEnvelope = λ cutoff observable time →
      ℚP.≤-trans
        (R343.selectedResponseBelowSourceEnvelope application
          cutoff observable time)
        (R343.sourceEnvelopeBelowSpectrumEnvelope application
          cutoff observable time)
  }

------------------------------------------------------------------------
-- Exact finite covariance upper, with no source-envelope coordinate.
------------------------------------------------------------------------

finiteSelectedUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectSelectedSpectralUpper base tests spectrumSource →
  ∀ cutoff observable time →
  let index = R281.indexFor spectrumSource observable time in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index) (R278.right tests index)
  ≤ R281.clusteringEnvelope spectrumSource observable time
finiteSelectedUpper
    {extension = extension} {base = base}
    {tests = tests} {spectrumSource = spectrumSource}
    direct cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    selectedBound =
      selectedResponseBelowSpectrumEnvelope direct cutoff observable time
    selectedToCovariance =
      R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
        base cutoff left right
  in
  subst
    (λ lower → lower ≤ R281.clusteringEnvelope spectrumSource observable time)
    selectedToCovariance
    selectedBound

------------------------------------------------------------------------
-- Terminal compiler: direct finite upper + standard ordered-limit closure.
------------------------------------------------------------------------

directSelectedSpectralUpperBuildsSubgapUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectSelectedSpectralUpper base tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = dataSet} →
  Gap.SubgapModeClusteringUpper
    (R281.asReconstructedClusteringSpectrum spectrumSource)
directSelectedSpectralUpperBuildsSubgapUpper
    {dataSet = dataSet} {extension = extension}
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    direct limitClosure energy mode time =
  let
    observable = R281.modeObservable spectrumSource energy mode
    index = R281.indexFor spectrumSource observable time
    sequence = λ cutoff →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R278.left tests index) (R278.right tests index)
    target =
      R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests index) (R278.right tests index)
    upper = R281.clusteringEnvelope spectrumSource observable time
  in
  limitClosure
    sequence target upper
    (R278.selectedConnectedCovarianceMagnitudeConverges
      extension tests index)
    (λ cutoff → finiteSelectedUpper direct cutoff observable time)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

directSelectedSpectralUpperIsTerminalConsumer : Bool
directSelectedSpectralUpperIsTerminalConsumer = true

sourceEnvelopeNotMandatoryAtTerminalABI : Bool
sourceEnvelopeNotMandatoryAtTerminalABI = true

sourceRootNotMandatoryAtTerminalABI : Bool
sourceRootNotMandatoryAtTerminalABI = true

sourceDistanceNotMandatoryAtTerminalABI : Bool
sourceDistanceNotMandatoryAtTerminalABI = true

round387CompilerConsumesDirectUpper : Bool
round387CompilerConsumesDirectUpper = true

r343CompilesToR387 : Bool
r343CompilesToR387 = true

directUpperRecoversSourceEnvelopeSemantics : Bool
directUpperRecoversSourceEnvelopeSemantics = false

freshYMDecayEstimateIntroduced : Bool
freshYMDecayEstimateIntroduced = false

round387DirectSelectedUpperLevel : ProofLevel
round387DirectSelectedUpperLevel = conditional

round387LimitClosureLevel : ProofLevel
round387LimitClosureLevel = R342.round342SelectedLimitUpperClosureLevel

round387CompilerLevel : ProofLevel
round387CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
