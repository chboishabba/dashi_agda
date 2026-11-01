{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ModeSelectedSubgapClusteringBidiExact where

------------------------------------------------------------------------
-- CMP116 SOURCE ENVELOPE -> MODE-SELECTED SUBGAP CLUSTERING
--
-- Highest-alpha source-native producer for the current spectral consumer.
--
-- Do NOT force the published CMP109/116 exponential envelope through the
-- historical coefficient-1 T2 rooted shell if the terminal consumer only needs
-- a fast upper for hypothetical subgap-mode observables.  Keep the source
-- prefactor/rate native and require only the proof-bearing same-spectrum welds:
--
--   source theorem on selected source directions
--     -> embed source magnitude into spectral Bound
--     -> same-spectrum convergence for that mode/time
--     -> source envelope <= spectral fast envelope
--     -> SubgapModeClusteringUpper
--     -> positive transfer-gap core.
--
-- This route is optional.  It does not invalidate the stronger global R304/R305
-- route or the T2 rooted-shell calibration route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276
import DASHI.Physics.YangMills.BalabanModeSelectedOneSidedClusteringLimitExact as Mode

record CMP116ModeSelectedSpectrumApplication
    {Observable Energy Bound Scale Volume Root SourceDirection : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    (source : Source.PublishedCMP116DifferentiatedLocalization
      Scale Volume Root SourceDirection ℚ)
    : Set₁ where
  field
    orderLimit : R276.UpperClosedConvergence Bound
    orderTransitive : ∀ {left middle right} →
      R276.LessEqual orderLimit left middle →
      R276.LessEqual orderLimit middle right →
      R276.LessEqual orderLimit left right

    embed : ℚ → Bound

    sourceOrderToLimitOrder : ∀ {left right} →
      Source.LessEqual source left right →
      R276.LessEqual orderLimit (embed left) (embed right)

    orderIsSpectrumOrder : ∀ left right →
      R276.LessEqual orderLimit left right ≡ Gap.LessEqual spectrum left right

    scaleOf : Nat → Scale
    volumeOf : Nat → Volume

    -- Only source directions needed by the hypothetical subgap mode are
    -- selected.  There is no all-observable source-direction obligation here.
    leftDirection :
      (energy : Energy) → Gap.SubgapMode spectrum energy → Nat → SourceDirection
    rightDirection :
      (energy : Energy) → Gap.SubgapMode spectrum energy → Nat → SourceDirection

    selectedPairAdmissible :
      ∀ cutoff energy mode time →
      Source.AdmissibleSourcePair source
        (scaleOf cutoff) (volumeOf cutoff)
        (leftDirection energy mode time)
        (rightDirection energy mode time)

    -- SAME-SPECTRUM identity at the limit: the finite source response is not
    -- promoted merely because it is called a correlation.
    embeddedSourceMagnitudeConvergesToSpectrum :
      ∀ energy mode time →
      R276.Converges orderLimit
        (λ cutoff → embed
          (Source.differentiatedMagnitude source
            (scaleOf cutoff) (volumeOf cutoff)
            (leftDirection energy mode time)
            (rightDirection energy mode time)))
        (Gap.connectedCorrelation spectrum
          (Gap.modeObservable spectrum energy mode) time)

    -- Consumer-relative envelope comparison.  The source prefactor/rate remain
    -- native; no coefficient-1 rooted-shell normalization is required here.
    embeddedSourceEnvelopeBelowSpectrumEnvelope :
      ∀ cutoff energy mode time →
      R276.LessEqual orderLimit
        (embed
          (Source.sourceEnvelope source
            (scaleOf cutoff) (volumeOf cutoff)
            (Source.sourceRoot source
              (scaleOf cutoff) (volumeOf cutoff)
              (leftDirection energy mode time)
              (rightDirection energy mode time))
            (Source.sourceDistance source
              (leftDirection energy mode time)
              (rightDirection energy mode time))))
        (Gap.clusteringEnvelope spectrum
          (Gap.modeObservable spectrum energy mode) time)

open CMP116ModeSelectedSpectrumApplication public

finiteModeSourceUpper :
  ∀ {Observable Energy Bound Scale Volume Root SourceDirection}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      Scale Volume Root SourceDirection ℚ} →
  (application : CMP116ModeSelectedSpectrumApplication spectrum source) →
  ∀ cutoff energy mode time →
  R276.LessEqual (orderLimit application)
    (embed application
      (Source.differentiatedMagnitude source
        (scaleOf application cutoff) (volumeOf application cutoff)
        (leftDirection application energy mode time)
        (rightDirection application energy mode time)))
    (Gap.clusteringEnvelope spectrum
      (Gap.modeObservable spectrum energy mode) time)
finiteModeSourceUpper {source = source} application cutoff energy mode time =
  orderTransitive application
    (sourceOrderToLimitOrder application
      (Source.sourceDifferentiatedLocalization source
        (scaleOf application cutoff)
        (volumeOf application cutoff)
        (leftDirection application energy mode time)
        (rightDirection application energy mode time)
        (selectedPairAdmissible application cutoff energy mode time)))
    (embeddedSourceEnvelopeBelowSpectrumEnvelope application
      cutoff energy mode time)

asModeSelectedFiniteCorrelationUpper :
  ∀ {Observable Energy Bound Scale Volume Root SourceDirection}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      Scale Volume Root SourceDirection ℚ} →
  CMP116ModeSelectedSpectrumApplication spectrum source →
  Mode.ModeSelectedFiniteCorrelationUpper spectrum
asModeSelectedFiniteCorrelationUpper {source = source} application = record
  { Mode.ModeSelectedFiniteCorrelationUpper.orderLimit = orderLimit application
  ; Mode.ModeSelectedFiniteCorrelationUpper.finiteModeCorrelation =
      λ cutoff energy mode time → embed application
        (Source.differentiatedMagnitude source
          (scaleOf application cutoff) (volumeOf application cutoff)
          (leftDirection application energy mode time)
          (rightDirection application energy mode time))
  ; Mode.ModeSelectedFiniteCorrelationUpper.finiteModeConvergesToSpectrumCorrelation =
      embeddedSourceMagnitudeConvergesToSpectrum application
  ; Mode.ModeSelectedFiniteCorrelationUpper.finiteModeUniformUpper =
      finiteModeSourceUpper application
  ; Mode.ModeSelectedFiniteCorrelationUpper.orderIsSpectrumOrder =
      orderIsSpectrumOrder application
  }

cmp116ModeSelectedApplicationBuildsSubgapUpper :
  ∀ {Observable Energy Bound Scale Volume Root SourceDirection}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      Scale Volume Root SourceDirection ℚ} →
  CMP116ModeSelectedSpectrumApplication spectrum source →
  Gap.SubgapModeClusteringUpper spectrum
cmp116ModeSelectedApplicationBuildsSubgapUpper application =
  Mode.modeSelectedContinuumUpper
    (asModeSelectedFiniteCorrelationUpper application)

cmp116ModeSelectedApplicationBuildsPositiveGapCore :
  ∀ {Observable Energy Bound Scale Volume Root SourceDirection}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      Scale Volume Root SourceDirection ℚ} →
  CMP116ModeSelectedSpectrumApplication spectrum source →
  Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum) →
  Gap.PositiveTransferGapCore spectrum
cmp116ModeSelectedApplicationBuildsPositiveGapCore application positive =
  Gap.positiveTransferGapCoreFromModeTests _
    (cmp116ModeSelectedApplicationBuildsSubgapUpper application)
    positive

record CMP116ModeSelectedBoundary : Set where
  constructor cmp116-mode-selected-boundary
  field
    coefficientOneRootedShellMandatory : Bool
    coefficientOneRootedShellMandatoryIsFalse :
      coefficientOneRootedShellMandatory ≡ false

    quarterHalfEnvelopeMandatory : Bool
    quarterHalfEnvelopeMandatoryIsFalse :
      quarterHalfEnvelopeMandatory ≡ false

    allObservableSourceDirectionsMandatory : Bool
    allObservableSourceDirectionsMandatoryIsFalse :
      allObservableSourceDirectionsMandatory ≡ false

    sameSpectrumConvergenceStillRequired : Bool
    sameSpectrumConvergenceStillRequiredIsTrue :
      sameSpectrumConvergenceStillRequired ≡ true

    sourceEnvelopeToSpectralEnvelopeStillRequired : Bool
    sourceEnvelopeToSpectralEnvelopeStillRequiredIsTrue :
      sourceEnvelopeToSpectralEnvelopeStillRequired ≡ true

    selectedModeSourceApplicabilityStillRequired : Bool
    selectedModeSourceApplicabilityStillRequiredIsTrue :
      selectedModeSourceApplicabilityStillRequired ≡ true

canonicalCMP116ModeSelectedBoundary : CMP116ModeSelectedBoundary
canonicalCMP116ModeSelectedBoundary =
  cmp116-mode-selected-boundary false refl false refl false refl true refl true refl true refl

cmp116ModeSelectedCompilerLevel : ProofLevel
cmp116ModeSelectedCompilerLevel = machineChecked

cmp116ModeSelectedSameSpectrumConvergenceLevel : ProofLevel
cmp116ModeSelectedSameSpectrumConvergenceLevel = conditional

cmp116ModeSelectedEnvelopeComparisonLevel : ProofLevel
cmp116ModeSelectedEnvelopeComparisonLevel = conditional

cmp116ModeSelectedApplicabilityLevel : ProofLevel
cmp116ModeSelectedApplicabilityLevel = conditional
