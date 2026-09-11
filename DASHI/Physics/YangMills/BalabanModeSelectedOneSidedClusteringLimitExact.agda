{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanModeSelectedOneSidedClusteringLimitExact where

------------------------------------------------------------------------
-- MODE-SELECTED ONE-SIDED LIMIT COMPILER
--
-- R276 predates the later least-privilege spectral reduction and quantifies its
-- finite/cutoff upper over every observable.  The actual terminal consumer in
-- `BalabanClayT5ClusteringToTransferGapExact` is smaller: only observables that
-- would witness a hypothetical positive subgap mode need the fast upper.
--
-- This module removes that global-observable overpayment while retaining every
-- theorem-bearing same-object coordinate:
--
--   * finite/cutoff sequence for the SAME mode observable;
--   * convergence to the SAME reconstructed spectral correlation;
--   * one-sided upper by the SAME spectral clustering envelope;
--   * exact order interpretation.
--
-- No clustering estimate is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276

record ModeSelectedFiniteCorrelationUpper
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    orderLimit : R276.UpperClosedConvergence Bound

    finiteModeCorrelation :
      Nat → (energy : Energy) → Gap.SubgapMode spectrum energy → Nat → Bound

    finiteModeConvergesToSpectrumCorrelation :
      ∀ energy mode time →
      R276.Converges orderLimit
        (λ cutoff → finiteModeCorrelation cutoff energy mode time)
        (Gap.connectedCorrelation spectrum
          (Gap.modeObservable spectrum energy mode) time)

    finiteModeUniformUpper :
      ∀ cutoff energy mode time →
      R276.LessEqual orderLimit
        (finiteModeCorrelation cutoff energy mode time)
        (Gap.clusteringEnvelope spectrum
          (Gap.modeObservable spectrum energy mode) time)

    orderIsSpectrumOrder : ∀ left right →
      R276.LessEqual orderLimit left right ≡ Gap.LessEqual spectrum left right

open ModeSelectedFiniteCorrelationUpper public

modeSelectedContinuumUpper :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  ModeSelectedFiniteCorrelationUpper spectrum →
  Gap.SubgapModeClusteringUpper spectrum
modeSelectedContinuumUpper {spectrum = spectrum} payment energy mode time =
  let
    genericUpper :
      R276.LessEqual (orderLimit payment)
        (Gap.connectedCorrelation spectrum
          (Gap.modeObservable spectrum energy mode) time)
        (Gap.clusteringEnvelope spectrum
          (Gap.modeObservable spectrum energy mode) time)
    genericUpper =
      R276.uniformUpperSurvivesLimit
        (orderLimit payment)
        (λ cutoff → finiteModeCorrelation payment cutoff energy mode time)
        (Gap.connectedCorrelation spectrum
          (Gap.modeObservable spectrum energy mode) time)
        (Gap.clusteringEnvelope spectrum
          (Gap.modeObservable spectrum energy mode) time)
        (finiteModeConvergesToSpectrumCorrelation payment energy mode time)
        (λ cutoff → finiteModeUniformUpper payment cutoff energy mode time)
  in
  subst
    (λ proposition → proposition)
    (orderIsSpectrumOrder payment
      (Gap.connectedCorrelation spectrum
        (Gap.modeObservable spectrum energy mode) time)
      (Gap.clusteringEnvelope spectrum
        (Gap.modeObservable spectrum energy mode) time))
    genericUpper

modeSelectedFiniteUpperBuildsPositiveGapCore :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  ModeSelectedFiniteCorrelationUpper spectrum →
  Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum) →
  Gap.PositiveTransferGapCore spectrum
modeSelectedFiniteUpperBuildsPositiveGapCore {spectrum = spectrum}
    payment positive =
  Gap.positiveTransferGapCoreFromModeTests spectrum
    (modeSelectedContinuumUpper payment) positive

record ModeSelectedBoundary : Set where
  constructor mode-selected-boundary
  field
    allObservableFiniteUpperMandatory : Bool
    allObservableFiniteUpperMandatoryIsFalse :
      allObservableFiniteUpperMandatory ≡ false

    allObservableContinuumClusteringMandatory : Bool
    allObservableContinuumClusteringMandatoryIsFalse :
      allObservableContinuumClusteringMandatory ≡ false

    sameSpectrumModeConvergenceStillRequired : Bool
    sameSpectrumModeConvergenceStillRequiredIsTrue :
      sameSpectrumModeConvergenceStillRequired ≡ true

    modeSelectedOneSidedUpperStillRequired : Bool
    modeSelectedOneSidedUpperStillRequiredIsTrue :
      modeSelectedOneSidedUpperStillRequired ≡ true

canonicalModeSelectedBoundary : ModeSelectedBoundary
canonicalModeSelectedBoundary =
  mode-selected-boundary false refl false refl true refl true refl

modeSelectedOneSidedLimitCompilerLevel : ProofLevel
modeSelectedOneSidedLimitCompilerLevel = machineChecked

modeSelectedSameSpectrumConvergenceLevel : ProofLevel
modeSelectedSameSpectrumConvergenceLevel = conditional

modeSelectedFiniteUpperLevel : ProofLevel
modeSelectedFiniteUpperLevel = conditional
