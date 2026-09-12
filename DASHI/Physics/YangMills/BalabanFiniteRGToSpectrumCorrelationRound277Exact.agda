{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRGToSpectrumCorrelationRound277Exact where

------------------------------------------------------------------------
-- ROUND277 / FINITE RG COVARIANCE -> SAME-SPECTRUM ONE-SIDED LIMIT
--
-- The repository already owns the finite covariance telescope and the
-- controlled/exceptional envelope compiler.  Do not re-prove them here.
--
-- This adapter exposes only the representation work needed to feed R276:
--   * a selected rational finite covariance for every cutoff/observable/time;
--   * its existing good/bad proof-bearing chain and budget;
--   * a rational physical envelope;
--   * an ordered embedding into the exact spectral Bound carrier;
--   * equality of the embedded envelope with the exact spectral envelope;
--   * convergence of the embedded finite covariance magnitude to the exact
--     spectral connected-correlation value.
--
-- Thus finite RG decay is not silently identified with continuum spectral
-- clustering.  That same-object convergence remains an explicit theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_; ∣_∣)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGGoodBadResidualEnvelopeExact as GoodBad
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276

record FiniteRGToSpectrumCorrelationWeld
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    orderLimit : R276.UpperClosedConvergence Bound

    embed : ℚ → Bound
    embedOrder : ∀ {left right} → left ≤ right →
      R276.LessEqual orderLimit (embed left) (embed right)

    orderIsSpectrumOrder : ∀ left right →
      R276.LessEqual orderLimit left right ≡
      Gap.LessEqual spectrum left right

    finiteCovariance : Nat → Observable → Nat → ℚ

    covarianceChain : ∀ cutoff observable time →
      GoodBad.GoodBadCovarianceChain
        (finiteCovariance cutoff observable time)

    covarianceBudget : ∀ cutoff observable time →
      GoodBad.GoodBadBudget
        (covarianceChain cutoff observable time)

    rationalPhysicalEnvelope : Observable → Nat → ℚ

    goodBadEnvelopeBelowPhysical : ∀ cutoff observable time →
      ∣ GoodBad.terminalCovariance
          (covarianceChain cutoff observable time) ∣
        + GoodBad.goodBudget (covarianceBudget cutoff observable time)
        + GoodBad.exceptionalBudget (covarianceBudget cutoff observable time)
      ≤ rationalPhysicalEnvelope observable time

    embeddedEnvelopeIsSpectrumEnvelope : ∀ observable time →
      embed (rationalPhysicalEnvelope observable time)
      ≡ Gap.clusteringEnvelope spectrum observable time

    embeddedFiniteMagnitudeConvergesToSpectrum : ∀ observable time →
      R276.Converges orderLimit
        (λ cutoff → embed ∣ finiteCovariance cutoff observable time ∣)
        (Gap.connectedCorrelation spectrum observable time)

open FiniteRGToSpectrumCorrelationWeld public

finiteRationalClusteringUpper :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    (weld : FiniteRGToSpectrumCorrelationWeld spectrum)
    cutoff observable time →
  ∣ finiteCovariance weld cutoff observable time ∣
  ≤ rationalPhysicalEnvelope weld observable time
finiteRationalClusteringUpper weld cutoff observable time =
  GoodBad.finiteRGClusteringFromGoodBadEnvelope
    (covarianceChain weld cutoff observable time)
    (covarianceBudget weld cutoff observable time)
    time
    (λ _ → rationalPhysicalEnvelope weld observable time)
    (goodBadEnvelopeBelowPhysical weld cutoff observable time)

finiteEmbeddedClusteringUpper :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    (weld : FiniteRGToSpectrumCorrelationWeld spectrum)
    cutoff observable time →
  R276.LessEqual (orderLimit weld)
    (embed weld ∣ finiteCovariance weld cutoff observable time ∣)
    (Gap.clusteringEnvelope spectrum observable time)
finiteEmbeddedClusteringUpper {spectrum = spectrum} weld cutoff observable time =
  let
    embedded :
      R276.LessEqual (orderLimit weld)
        (embed weld ∣ finiteCovariance weld cutoff observable time ∣)
        (embed weld (rationalPhysicalEnvelope weld observable time))
    embedded = embedOrder weld
      (finiteRationalClusteringUpper weld cutoff observable time)
  in
  subst
    (λ upper →
      R276.LessEqual (orderLimit weld)
        (embed weld ∣ finiteCovariance weld cutoff observable time ∣)
        upper)
    (embeddedEnvelopeIsSpectrumEnvelope weld observable time)
    embedded

asSameSpectrumFiniteCorrelationUpper :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  FiniteRGToSpectrumCorrelationWeld spectrum →
  R276.SameSpectrumFiniteCorrelationUpper spectrum
asSameSpectrumFiniteCorrelationUpper weld = record
  { R276.SameSpectrumFiniteCorrelationUpper.orderLimit = orderLimit weld
  ; R276.SameSpectrumFiniteCorrelationUpper.finiteConnectedCorrelation =
      λ cutoff observable time →
        embed weld ∣ finiteCovariance weld cutoff observable time ∣
  ; R276.SameSpectrumFiniteCorrelationUpper.finiteConvergesToSpectrumCorrelation =
      embeddedFiniteMagnitudeConvergesToSpectrum weld
  ; R276.SameSpectrumFiniteCorrelationUpper.finiteUniformClusteringUpper =
      finiteEmbeddedClusteringUpper weld
  ; R276.SameSpectrumFiniteCorrelationUpper.orderIsSpectrumOrder =
      orderIsSpectrumOrder weld
  }

compileFiniteRGEnvelopeToSpectrumClustering :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  FiniteRGToSpectrumCorrelationWeld spectrum →
  Gap.ClusteringUpperBound spectrum
compileFiniteRGEnvelopeToSpectrumClustering weld =
  R276.compileFiniteUniformUpperToSpectrumClustering
    (asSameSpectrumFiniteCorrelationUpper weld)

record Round277Boundary : Set where
  constructor round277-boundary
  field
    covarianceTelescopeReprovedHere : Bool
    covarianceTelescopeReprovedHereIsFalse :
      covarianceTelescopeReprovedHere ≡ false

    goodBadEnvelopeAlgebraReprovedHere : Bool
    goodBadEnvelopeAlgebraReprovedHereIsFalse :
      goodBadEnvelopeAlgebraReprovedHere ≡ false

    finiteRGEqualsSpectrumCorrelationByName : Bool
    finiteRGEqualsSpectrumCorrelationByNameIsFalse :
      finiteRGEqualsSpectrumCorrelationByName ≡ false

    sameSpectrumConvergenceStillRequired : Bool
    sameSpectrumConvergenceStillRequiredIsTrue :
      sameSpectrumConvergenceStillRequired ≡ true

canonicalRound277Boundary : Round277Boundary
canonicalRound277Boundary =
  round277-boundary false refl false refl false refl true refl

round277FiniteRGEnvelopeAdapterLevel : ProofLevel
round277FiniteRGEnvelopeAdapterLevel = machineChecked

round277PhysicalGoodRegionContractionLevel : ProofLevel
round277PhysicalGoodRegionContractionLevel = conditional

round277PhysicalExceptionalSuppressionLevel : ProofLevel
round277PhysicalExceptionalSuppressionLevel = conditional

round277FiniteRGToSameSpectrumConvergenceLevel : ProofLevel
round277FiniteRGToSameSpectrumConvergenceLevel = conditional
