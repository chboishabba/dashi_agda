module DASHI.Culture.IntellectualReceptionPrecisionFiltrationFirstDivergenceExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / PRECISION FILTRATION + FIRST DIVERGENCE
--
-- Replace the two-level refinement fixture by a finite filtration of observation
-- selectors.  A certificate's projected disposition is stable while every
-- selected supported coordinate is observer-shared.  The first stage exposing
-- a supported divergent coordinate carries an explicit first-divergence receipt
-- and generates selective reopening.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionObserverDerivedSupportPartitionExact as Observer
import DASHI.Culture.IntellectualReceptionObservationPrecisionRefinementExact as Precision

------------------------------------------------------------------------
-- 1. A three-stage finite filtration.
------------------------------------------------------------------------

data PrecisionStage : Set where
  stage0Present
  stage1PresentFuture
  stage2PresentFutureAuthority
  : PrecisionStage

data SelectedAtStage : PrecisionStage → Reuse.PrefixCoordinate → Set where
  s0Present : SelectedAtStage stage0Present Reuse.presentCoordinate

  s1Present : SelectedAtStage stage1PresentFuture Reuse.presentCoordinate
  s1Future : SelectedAtStage stage1PresentFuture Reuse.futureCoordinate

  s2Present : SelectedAtStage stage2PresentFutureAuthority Reuse.presentCoordinate
  s2Future : SelectedAtStage stage2PresentFutureAuthority Reuse.futureCoordinate
  s2Authority : SelectedAtStage stage2PresentFutureAuthority Reuse.authorityCoordinate

data NextStage : PrecisionStage → PrecisionStage → Set where
  next01 : NextStage stage0Present stage1PresentFuture
  next12 : NextStage stage1PresentFuture stage2PresentFutureAuthority

selectedMonotoneAcrossNext :
  ∀ {earlier later coordinate} →
  NextStage earlier later →
  SelectedAtStage earlier coordinate →
  SelectedAtStage later coordinate
selectedMonotoneAcrossNext next01 s0Present = s1Present
selectedMonotoneAcrossNext next12 s1Present = s2Present
selectedMonotoneAcrossNext next12 s1Future = s2Future

------------------------------------------------------------------------
-- 2. Observer agreement at each filtration stage.
------------------------------------------------------------------------

AgreeAtStage : PrecisionStage → Set
AgreeAtStage stage =
  ∀ {coordinate} →
  SelectedAtStage stage coordinate →
  Observer.SharedByObserver coordinate

stage0Agreement : AgreeAtStage stage0Present
stage0Agreement s0Present = Observer.presentSharedByObserver

stage1Agreement : AgreeAtStage stage1PresentFuture
stage1Agreement s1Present = Observer.presentSharedByObserver
stage1Agreement s1Future = Observer.futureSharedByObserver

stage2AgreementImpossible : AgreeAtStage stage2PresentFutureAuthority → ⊥
stage2AgreementImpossible agreement =
  Observer.authorityDivergentByObserver (agreement s2Authority)

agreementDescendsOneStage :
  ∀ {earlier later} →
  NextStage earlier later →
  AgreeAtStage later →
  AgreeAtStage earlier
agreementDescendsOneStage next agreement selected =
  agreement (selectedMonotoneAcrossNext next selected)

------------------------------------------------------------------------
-- 3. Precision-projected support at an arbitrary stage.
------------------------------------------------------------------------

record ProjectedSupportedAtStage
    (stage : PrecisionStage)
    (support : Reuse.CertificateSupport)
    (coordinate : Reuse.PrefixCoordinate) : Set where
  constructor projected-supported-at-stage
  field
    supported : Reuse.SupportedCoordinate support coordinate
    selected : SelectedAtStage stage coordinate

open ProjectedSupportedAtStage public

ProjectedSupportSharedAtStage :
  PrecisionStage → Reuse.CertificateSupport → Set
ProjectedSupportSharedAtStage stage support =
  ∀ {coordinate} →
  ProjectedSupportedAtStage stage support coordinate →
  Observer.SharedByObserver coordinate

authoritySupportSharedAtStage0 :
  ProjectedSupportSharedAtStage
    stage0Present Reuse.authoritySensitiveSupport
authoritySupportSharedAtStage0
  (projected-supported-at-stage Reuse.supportPresent s0Present) =
    Observer.presentSharedByObserver

authoritySupportSharedAtStage1 :
  ProjectedSupportSharedAtStage
    stage1PresentFuture Reuse.authoritySensitiveSupport
authoritySupportSharedAtStage1
  (projected-supported-at-stage Reuse.supportPresent s1Present) =
    Observer.presentSharedByObserver
authoritySupportSharedAtStage1
  (projected-supported-at-stage Reuse.supportFuture s1Future) =
    Observer.futureSharedByObserver

------------------------------------------------------------------------
-- 4. First supported divergence depth.
------------------------------------------------------------------------

record FirstSupportedDivergenceAt
    (support : Reuse.CertificateSupport)
    (stage : PrecisionStage) : Set where
  constructor first-supported-divergence-at
  field
    coordinate : Reuse.PrefixCoordinate
    supported : Reuse.SupportedCoordinate support coordinate
    selectedHere : SelectedAtStage stage coordinate
    divergentHere : Observer.DivergentByObserver coordinate
    absentAtStage0 : SelectedAtStage stage0Present coordinate → ⊥
    absentAtStage1 : SelectedAtStage stage1PresentFuture coordinate → ⊥

open FirstSupportedDivergenceAt public

authorityFirstDivergesAtStage2 :
  FirstSupportedDivergenceAt
    Reuse.authoritySensitiveSupport
    stage2PresentFutureAuthority
authorityFirstDivergesAtStage2 =
  first-supported-divergence-at
    Reuse.authorityCoordinate
    Reuse.supportAuthority
    s2Authority
    Observer.authorityDivergentByObserver
    (λ ())
    (λ ())

------------------------------------------------------------------------
-- 5. Disposition is stable before first divergence and reopens at it.
------------------------------------------------------------------------

data FiltrationProjectedDisposition
    (stage : PrecisionStage)
    (support : Reuse.CertificateSupport) : Set where
  retainBeforeDivergence :
    ProjectedSupportSharedAtStage stage support →
    FiltrationProjectedDisposition stage support

  reopenAtFirstDivergence :
    FirstSupportedDivergenceAt support stage →
    FiltrationProjectedDisposition stage support

authorityProjectionRetainedAtStage0 :
  FiltrationProjectedDisposition
    stage0Present Reuse.authoritySensitiveSupport
authorityProjectionRetainedAtStage0 =
  retainBeforeDivergence authoritySupportSharedAtStage0

authorityProjectionRetainedAtStage1 :
  FiltrationProjectedDisposition
    stage1PresentFuture Reuse.authoritySensitiveSupport
authorityProjectionRetainedAtStage1 =
  retainBeforeDivergence authoritySupportSharedAtStage1

authorityProjectionReopensAtStage2 :
  FiltrationProjectedDisposition
    stage2PresentFutureAuthority Reuse.authoritySensitiveSupport
authorityProjectionReopensAtStage2 =
  reopenAtFirstDivergence authorityFirstDivergesAtStage2

stage0CannotAlreadyExposeAuthority :
  SelectedAtStage stage0Present Reuse.authorityCoordinate → ⊥
stage0CannotAlreadyExposeAuthority ()

stage1CannotAlreadyExposeAuthority :
  SelectedAtStage stage1PresentFuture Reuse.authorityCoordinate → ⊥
stage1CannotAlreadyExposeAuthority ()

------------------------------------------------------------------------
-- 6. First divergence generates the actual reopening dependency cone.
------------------------------------------------------------------------

module FirstDivergenceReopening where

  data Artifact : Set where
    firstDivergenceArtifact
    stage2ProjectionCertificate
    downstreamCertificate
    : Artifact

  data Depends : Artifact → Artifact → Set where
    firstDivergenceCreatesDependency :
      FirstSupportedDivergenceAt
        Reuse.authoritySensitiveSupport
        stage2PresentFutureAuthority →
      Depends firstDivergenceArtifact stage2ProjectionCertificate

    stage2ProjectionFeedsDownstream :
      Depends stage2ProjectionCertificate downstreamCertificate

  firstDivergenceReopensStage2Projection :
    Affected.ReopeningObligation
      Depends firstDivergenceArtifact stage2ProjectionCertificate
  firstDivergenceReopensStage2Projection =
    Affected.oneEdgeCreatesReopeningObligation
      (firstDivergenceCreatesDependency authorityFirstDivergesAtStage2)

  firstDivergenceReopensDownstream :
    Affected.ReopeningObligation
      Depends firstDivergenceArtifact downstreamCertificate
  firstDivergenceReopensDownstream =
    Affected.obligationsCompose
      firstDivergenceReopensStage2Projection
      (Affected.oneEdgeCreatesReopeningObligation
        stage2ProjectionFeedsDownstream)

------------------------------------------------------------------------
-- 7. Bridge back to the two-level precision owner.
------------------------------------------------------------------------

stage1MatchesCoarseSelectorOnPresent :
  Precision.SelectedAt
    Precision.coarsePresentFuture
    Reuse.presentCoordinate
stage1MatchesCoarseSelectorOnPresent = Precision.coarseSelectPresent

stage1MatchesCoarseSelectorOnFuture :
  Precision.SelectedAt
    Precision.coarsePresentFuture
    Reuse.futureCoordinate
stage1MatchesCoarseSelectorOnFuture = Precision.coarseSelectFuture

stage2MatchesFineSelectorOnAuthority :
  Precision.SelectedAt
    Precision.finePresentFutureAuthority
    Reuse.authorityCoordinate
stage2MatchesFineSelectorOnAuthority = Precision.fineSelectAuthority

------------------------------------------------------------------------
-- 8. No-promotion boundaries.
------------------------------------------------------------------------

data FirstDivergenceDepthPromotesPAdicValuation : Set where
data FirstDivergenceDepthPromotesHistoricalChangePoint : Set where
data StableProjectionPromotesFullCertificateRetention : Set where

firstDivergenceDepthDoesNotPromotePAdicValuation :
  FirstDivergenceDepthPromotesPAdicValuation → ⊥
firstDivergenceDepthDoesNotPromotePAdicValuation ()

firstDivergenceDepthDoesNotPromoteHistoricalChangePoint :
  FirstDivergenceDepthPromotesHistoricalChangePoint → ⊥
firstDivergenceDepthDoesNotPromoteHistoricalChangePoint ()

stableProjectionDoesNotPromoteFullCertificateRetention :
  StableProjectionPromotesFullCertificateRetention → ⊥
stableProjectionDoesNotPromoteFullCertificateRetention ()

------------------------------------------------------------------------
-- 9. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionPrecisionFiltrationFirstDivergenceBoundary : Set where
  constructor intellectual-reception-precision-filtration-first-divergence-boundary
  field
    precisionLevelsFormExplicitFiniteFiltration : Bool
    selectedCoordinatesGrowMonotonically : Bool
    projectedDispositionStableBeforeFirstDivergence : Bool
    firstDivergenceRequiresSupportedCoordinate : Bool
    firstDivergenceRequiresObserverInequality : Bool
    firstDivergenceReopensProjection : Bool
    firstDivergenceCanReopenDownstream : Bool
    firstDivergenceDepthIsLiteralPAdicValuation : Bool
    firstDivergenceDepthIsHistoricalChangePoint : Bool
    stableProjectionMeansFullCertificateRetention : Bool
    sourceAttributionBoundarySurvivesFiltration : Bool

canonicalIntellectualReceptionPrecisionFiltrationFirstDivergenceBoundary :
  IntellectualReceptionPrecisionFiltrationFirstDivergenceBoundary
canonicalIntellectualReceptionPrecisionFiltrationFirstDivergenceBoundary =
  intellectual-reception-precision-filtration-first-divergence-boundary
    true true true true true true true false false false true
