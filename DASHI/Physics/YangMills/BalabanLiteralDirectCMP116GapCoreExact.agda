{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralDirectCMP116GapCoreExact where

------------------------------------------------------------------------
-- LITERAL B CORE FROM THE ACTUAL T5 COVARIANCE / CMP116 SHELL ROUTE
--
-- This bypasses the higher-level PublishedSelectedCMP116Producer adapter.
-- The finite object is the exact T5 covariance consumed by R278; R284 proves
-- continuum clustering on the exact R281 covariance spectrum carrier; the
-- canonical mode-selected contradiction then yields PositiveTransferGapCore.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

literalDirectCMP116BuildsPositiveTransferGapCore :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R284.DirectT5ContinuumClusteringPayment
    dataSet extension tests source →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum source)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum source)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum source)
literalDirectCMP116BuildsPositiveTransferGapCore
    {source = source} clustering positive =
  Gap.positiveTransferGapCoreFromModeTests
    (R281.asReconstructedClusteringSpectrum source)
    (Gap.globalClusteringUpperImpliesSubgapModeUpper
      (R281.asReconstructedClusteringSpectrum source)
      (R284.compileDirectCMP116ToContinuumClustering clustering))
    positive

literalDirectCMP116GapCoreCompilerLevel : ProofLevel
literalDirectCMP116GapCoreCompilerLevel = machineChecked

-- Literal producer boundaries left on this route:
-- * the exact two-source CMP116 shell on the selected T5 covariance;
-- * selected support distance = Euclidean time;
-- * actual reconstructed-spectrum lower/slow-rate semantics;
-- * positivity of the selected physical gap threshold.
literalDirectCMP116ShellLevel : ProofLevel
literalDirectCMP116ShellLevel = R284.round284LiteralTwoSourceCMP116ShellLevel

literalDirectCMP116SpectrumInputsLevel : ProofLevel
literalDirectCMP116SpectrumInputsLevel =
  R281.round281PhysicalSpectralRepresentationAndRateInputsLevel
