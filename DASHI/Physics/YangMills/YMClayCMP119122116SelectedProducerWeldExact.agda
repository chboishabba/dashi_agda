{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCMP119122116SelectedProducerWeldExact where

------------------------------------------------------------------------
-- 2026-11-06: ACTUAL EXISTING 119/122/116 REUSE, NOT RE-DERIVATION.
--
-- 1. One beta-driven CMP119 complete-density source produces both its
--    CMP122-compatible coupling history and its exact SAME CMP109/116
--    effective potential / localized-component sum.  This combines
--    ALREADY source-written true equalities: no second trajectory, no
--    arbitrary post-hoc effective-action equality, no external axiom.
--
-- 2. One existing R342 literal selected CMP116 source produces BOTH
--    finite original selected covariance decay (R467) and, once the
--    existing selected-limit / positive-energy semantics are supplied,
--    the ORIGINAL R479 positive transfer gap.  NO second R467
--    localization record, no alternative covariance or OS Hamiltonian.
--
-- These are actual Agda proof TERMS, but no pinned kernel receipt yet.
-- They do not identify (1) with the original continuous SU(N) Wilson
-- Gibbs measure or construct the missing literal CMP116 source estimate.
--
-- CMP119 1988, CMP116 1988, CMP122 1989, original DASHI donors.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source122
import DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact as Local
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as Limit
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectoryToPublishedLiteralR467Exact as Bridge
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact as R467
import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralToGapRound479Exact as R479
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

-- Proven source coupling is literal beta history; the potential is
-- simultaneously the literal CMP119 density's localized CMP116 sum.
-- This DOES NOT claim the source density has been identified with
-- the original full Wilson/Gibbs/Haar field.
cmp119122BetaAndCMP116PotentialSameSource :
  ∀ {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (family : Local.BetaDrivenLocalizedEffectiveActionFamily inputs) →
  (∀ scale →
    Source122.couplingAt (Beta.betaDrivenCompleteDensityFlow inputs) scale
    ≡ History.couplingAt (Beta.betaHistory inputs) scale)
  ×
  (∀ scale volume background →
    Continue.cmp109EffectivePotential
      (Local.asCMP109116Continuation family) scale volume background
    ≡
    Finite.sumFunctions
      (Finite.mapList
        (Local.physicalLocalizedActivity family scale volume)
        (Local.components family scale volume))
      background)
cmp119122BetaAndCMP116PotentialSameSource inputs family =
  (λ scale → Beta.sourceCouplingIsBetaHistoryCoupling inputs scale)
  ,
  (λ scale volume background →
    trans
      (Local.cmp109PotentialIsLiteralBetaDrivenDensityPotential
        family scale volume background)
      (Local.densityPotentialIsLocalizedCompositeSum
        family scale volume background))
  where
  open import Relation.Binary.PropositionalEquality using (trans)

-- R342 owns the LITERAL same mixed-J source. R467 and R479 are
-- ALREADY complete theorem compilers on that exact source and its OS
-- selected upper-closure.  Avoid duplicating the source-facing
-- absolute localization and physical envelope fields.
sameLiteralR342SourceYieldsR479TransferGap :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : Radius.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R342.LiteralTrajectoryCMP116Source base demands tests spectrumSource →
  Limit.SelectedLimitUpperClosure {dataSet = dataSet} →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
sameLiteralR342SourceYieldsR479TransferGap
  source limitClosure positiveEnergy =
  R479.publishedLiteralSelectedBuildsPositiveTransferGap
    (Bridge.asPublishedLiteralSelectedLocalization source)
    limitClosure positiveEnergy

-- Exact *finite selected* covariance, same R342 source and physical
-- spectrum envelope, no fake intermediate marked covariance carrier.
sameLiteralR342SourceFiniteCovarianceDecay :
  ∀ {Measure TestObservable SpectralObservable Energy
      dataSet extension base demands tests spectrumSource}
    (source : R342.LiteralTrajectoryCMP116Source
      {Measure = Measure} {TestObservable = TestObservable}
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      {dataSet = dataSet} {extension = extension}
      base demands tests spectrumSource) →
  ∀ cutoff observable time →
  let index = R281.indexFor spectrumSource observable time in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index)
    (R278.right tests index)
  ≤
  R281.clusteringEnvelope spectrumSource observable time
sameLiteralR342SourceFiniteCovarianceDecay source =
  R467.finiteConnectedCovarianceLocalization
    (Bridge.asPublishedLiteralSelectedLocalization source)
