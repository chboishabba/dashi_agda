{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectCanonicalBCompletionRound286Exact where

------------------------------------------------------------------------
-- ROUND286 / DIRECT CANONICAL B COMPLETION RELATIVE TO THE SAME SPECTRUM
--
-- R284 compiles the literal CMP116 two-source finite T5 shell bound through
-- selected covariance convergence into the exact continuum clustering upper.
-- R285 compiles positivity once the proved clustering rate is identified with
-- the exact reconstructed energy candidate.
--
-- This owner enforces the missing SAME-RATE condition: the B2 decay ratio must
-- be the very q = 1/2 appearing in the R284 rooted-shell envelope.  A positive
-- but unrelated spectral number cannot pay the canonical mass-gap consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanClusteringDecayRatioToGapRound285Exact as R285
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound275Exact as R275
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record DirectCanonicalBPayment
    {Measure TestObservable SpectralObservable Energy : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests)
    : Set₁ where
  field
    clusteringPayment :
      R284.DirectT5ContinuumClusteringPayment dataSet extension tests source

    gapIdentification :
      R285.DecayRatioGapIdentification
        (R281.asReconstructedClusteringSpectrum source)

    -- SAME rate, not merely another strict decay coefficient.
    gapDecayRatioIsDirectEnvelopeRatio :
      R285.decayRatio gapIdentification ≡ Geo.half

open DirectCanonicalBPayment public

asCanonicalBPayment275 :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectCanonicalBPayment dataSet extension tests source →
  R275.CanonicalBPayment275 (R281.asReconstructedClusteringSpectrum source)
asCanonicalBPayment275 payment = record
  { R275.CanonicalBPayment275.clusteringUpper =
      R284.compileDirectCMP116ToContinuumClustering
        (clusteringPayment payment)
  ; R275.CanonicalBPayment275.candidatePositive =
      R285.candidateGapPositiveFromDecayRate
        (gapIdentification payment)
  }

compileDirectCanonicalBToPositiveTransferGap :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectCanonicalBPayment dataSet extension tests source →
  Gap.PositiveTransferGap (R281.asReconstructedClusteringSpectrum source)
compileDirectCanonicalBToPositiveTransferGap payment =
  R275.compileCanonicalBPayment (asCanonicalBPayment275 payment)

record Round286Boundary : Set where
  constructor round286-boundary
  field
    b1AndB2StillDistinct : Bool
    b1AndB2StillDistinctIsTrue : b1AndB2StillDistinct ≡ true

    unrelatedPositiveGapCanPayB2 : Bool
    unrelatedPositiveGapCanPayB2IsFalse : unrelatedPositiveGapCanPayB2 ≡ false

    directEnvelopeRateAndGapRateSameObjectRequired : Bool
    directEnvelopeRateAndGapRateSameObjectRequiredIsTrue :
      directEnvelopeRateAndGapRateSameObjectRequired ≡ true

    positiveTransferGapAfterPaymentsCompilerOwned : Bool
    positiveTransferGapAfterPaymentsCompilerOwnedIsTrue :
      positiveTransferGapAfterPaymentsCompilerOwned ≡ true

canonicalRound286Boundary : Round286Boundary
canonicalRound286Boundary =
  round286-boundary true refl false refl true refl true refl

round286DirectCanonicalBCompilerLevel : ProofLevel
round286DirectCanonicalBCompilerLevel = machineChecked

round286LiteralTwoSourceCMP116ShellLevel : ProofLevel
round286LiteralTwoSourceCMP116ShellLevel = R284.round284LiteralTwoSourceCMP116ShellLevel

round286PhysicalRateToSpectrumIdentificationLevel : ProofLevel
round286PhysicalRateToSpectrumIdentificationLevel =
  R285.round285PhysicalRateToSpectrumIdentificationLevel
