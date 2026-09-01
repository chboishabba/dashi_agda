module DASHI.Culture.IntellectualReceptionObservationPrecisionRefinementExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / OBSERVATION-PRECISION REFINEMENT
--
-- Observation precision is an explicit selector over coordinates.  Refining
-- precision exposes additional coordinates but does not change the underlying
-- fine histories.  Agreement at finer precision implies agreement at every
-- coarser selected coordinate.
--
-- A full certificate support is never silently treated as shared merely because
-- one of its coordinates is hidden.  Instead we distinguish the support visible
-- at a given precision.  A precision-projected certificate can therefore be
-- retained coarsely and reopened after refinement exposes a divergent supported
-- coordinate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal
import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionObserverDerivedSupportPartitionExact as Observer

------------------------------------------------------------------------
-- 1. Explicit precision selector and refinement order.
------------------------------------------------------------------------

data ObservationPrecision : Set where
  coarsePresentFuture
  finePresentFutureAuthority
  : ObservationPrecision

data SelectedAt : ObservationPrecision → Reuse.PrefixCoordinate → Set where
  coarseSelectPresent : SelectedAt coarsePresentFuture Reuse.presentCoordinate
  coarseSelectFuture : SelectedAt coarsePresentFuture Reuse.futureCoordinate

  fineSelectPresent : SelectedAt finePresentFutureAuthority Reuse.presentCoordinate
  fineSelectFuture : SelectedAt finePresentFutureAuthority Reuse.futureCoordinate
  fineSelectAuthority : SelectedAt finePresentFutureAuthority Reuse.authorityCoordinate

record PrecisionRefines
    (coarse fine : ObservationPrecision) : Set where
  constructor precision-refines
  field
    selectedMonotone :
      ∀ {coordinate} →
      SelectedAt coarse coordinate →
      SelectedAt fine coordinate

open PrecisionRefines public

coarseRefinesToFine :
  PrecisionRefines coarsePresentFuture finePresentFutureAuthority
coarseRefinesToFine =
  precision-refines λ
    { coarseSelectPresent → fineSelectPresent
    ; coarseSelectFuture → fineSelectFuture
    }

------------------------------------------------------------------------
-- 2. History agreement is precision-indexed.
------------------------------------------------------------------------

AgreeAtPrecision : ObservationPrecision → Set
AgreeAtPrecision precision =
  ∀ {coordinate} →
  SelectedAt precision coordinate →
  Observer.SharedByObserver coordinate

coarseAgreement : AgreeAtPrecision coarsePresentFuture
coarseAgreement coarseSelectPresent = Observer.presentSharedByObserver
coarseAgreement coarseSelectFuture = Observer.futureSharedByObserver

fineAgreementImpossible : AgreeAtPrecision finePresentFutureAuthority → ⊥
fineAgreementImpossible agreement =
  Observer.authorityDivergentByObserver
    (agreement fineSelectAuthority)

agreementDescendsAlongRefinement :
  ∀ {coarse fine} →
  PrecisionRefines coarse fine →
  AgreeAtPrecision fine →
  AgreeAtPrecision coarse
agreementDescendsAlongRefinement refinement agreement selected =
  agreement (selectedMonotone refinement selected)

fineAgreementWouldImplyCoarseAgreement :
  AgreeAtPrecision finePresentFutureAuthority →
  AgreeAtPrecision coarsePresentFuture
fineAgreementWouldImplyCoarseAgreement =
  agreementDescendsAlongRefinement coarseRefinesToFine

------------------------------------------------------------------------
-- 3. The visible projection of certificate support depends on precision.
------------------------------------------------------------------------

record ProjectedSupportedCoordinate
    (precision : ObservationPrecision)
    (support : Reuse.CertificateSupport)
    (coordinate : Reuse.PrefixCoordinate) : Set where
  constructor projected-supported-coordinate
  field
    supported : Reuse.SupportedCoordinate support coordinate
    selected : SelectedAt precision coordinate

open ProjectedSupportedCoordinate public

ProjectedSupportContainedInShared :
  ObservationPrecision →
  Reuse.CertificateSupport →
  Set
ProjectedSupportContainedInShared precision support =
  ∀ {coordinate} →
  ProjectedSupportedCoordinate precision support coordinate →
  Observer.SharedByObserver coordinate

coarseAuthoritySensitiveProjectionContained :
  ProjectedSupportContainedInShared
    coarsePresentFuture
    Reuse.authoritySensitiveSupport
coarseAuthoritySensitiveProjectionContained
  (projected-supported-coordinate Reuse.supportPresent coarseSelectPresent) =
    Observer.presentSharedByObserver
coarseAuthoritySensitiveProjectionContained
  (projected-supported-coordinate Reuse.supportFuture coarseSelectFuture) =
    Observer.futureSharedByObserver

------------------------------------------------------------------------
-- 4. Refinement exposes the previously hidden supported authority coordinate.
------------------------------------------------------------------------

record NewlyExposedSupportedCoordinate
    (coarse fine : ObservationPrecision)
    (support : Reuse.CertificateSupport) : Set where
  constructor newly-exposed-supported-coordinate
  field
    coordinate : Reuse.PrefixCoordinate
    supported : Reuse.SupportedCoordinate support coordinate
    selectedFine : SelectedAt fine coordinate
    notSelectedCoarse : SelectedAt coarse coordinate → ⊥

open NewlyExposedSupportedCoordinate public

authorityNewlyExposedByFinePrecision :
  NewlyExposedSupportedCoordinate
    coarsePresentFuture
    finePresentFutureAuthority
    Reuse.authoritySensitiveSupport
authorityNewlyExposedByFinePrecision =
  newly-exposed-supported-coordinate
    Reuse.authorityCoordinate
    Reuse.supportAuthority
    fineSelectAuthority
    λ ()

record NewlyExposedSupportIntersectsDivergence
    (coarse fine : ObservationPrecision)
    (support : Reuse.CertificateSupport) : Set where
  constructor newly-exposed-support-intersects-divergence
  field
    exposed : NewlyExposedSupportedCoordinate coarse fine support
    divergent : Observer.DivergentByObserver
      (NewlyExposedSupportedCoordinate.coordinate exposed)

open NewlyExposedSupportIntersectsDivergence public

authorityRefinementExposesDivergence :
  NewlyExposedSupportIntersectsDivergence
    coarsePresentFuture
    finePresentFutureAuthority
    Reuse.authoritySensitiveSupport
authorityRefinementExposesDivergence =
  newly-exposed-support-intersects-divergence
    authorityNewlyExposedByFinePrecision
    Observer.authorityDivergentByObserver

------------------------------------------------------------------------
-- 5. Precision-projected retain/reopen is one refinement-aware calculus.
------------------------------------------------------------------------

data PrecisionProjectedDisposition
    (precision : ObservationPrecision)
    (support : Reuse.CertificateSupport) : Set where
  retainProjected :
    ProjectedSupportContainedInShared precision support →
    PrecisionProjectedDisposition precision support

  reopenProjected :
    ∀ {coarse} →
    NewlyExposedSupportIntersectsDivergence coarse precision support →
    PrecisionProjectedDisposition precision support

coarseAuthoritySensitiveProjectionRetained :
  PrecisionProjectedDisposition
    coarsePresentFuture
    Reuse.authoritySensitiveSupport
coarseAuthoritySensitiveProjectionRetained =
  retainProjected coarseAuthoritySensitiveProjectionContained

fineAuthoritySensitiveProjectionReopened :
  PrecisionProjectedDisposition
    finePresentFutureAuthority
    Reuse.authoritySensitiveSupport
fineAuthoritySensitiveProjectionReopened =
  reopenProjected authorityRefinementExposesDivergence

------------------------------------------------------------------------
-- 6. Reopening is operational: newly exposed divergence propagates downstream.
------------------------------------------------------------------------

module PrecisionRefinementReopening where

  data Artifact : Set where
    newlyExposedCoordinateArtifact
    refinedProjectionCertificate
    downstreamCertificate
    : Artifact

  data Depends : Artifact → Artifact → Set where
    newlyExposedDivergenceCreatesDependency :
      NewlyExposedSupportIntersectsDivergence
        coarsePresentFuture
        finePresentFutureAuthority
        Reuse.authoritySensitiveSupport →
      Depends newlyExposedCoordinateArtifact refinedProjectionCertificate

    refinedProjectionFeedsDownstream :
      Depends refinedProjectionCertificate downstreamCertificate

  refinementCreatesReopening :
    Affected.ReopeningObligation
      Depends newlyExposedCoordinateArtifact refinedProjectionCertificate
  refinementCreatesReopening =
    Affected.oneEdgeCreatesReopeningObligation
      (newlyExposedDivergenceCreatesDependency
        authorityRefinementExposesDivergence)

  refinementReopensDownstream :
    Affected.ReopeningObligation
      Depends newlyExposedCoordinateArtifact downstreamCertificate
  refinementReopensDownstream =
    Affected.obligationsCompose
      refinementCreatesReopening
      (Affected.oneEdgeCreatesReopeningObligation
        refinedProjectionFeedsDownstream)

------------------------------------------------------------------------
-- 7. Exact least-privilege boundary: projected retention is not full retention.
------------------------------------------------------------------------

data ProjectedRetentionPromotesFullSupportRetention : Set where
data PrecisionRefinementPromotesHistoryChange : Set where
data PrecisionDepthPromotesPAdicValuation : Set where

aProjectedRetentionDoesNotPromoteFullSupportRetention :
  ProjectedRetentionPromotesFullSupportRetention → ⊥
aProjectedRetentionDoesNotPromoteFullSupportRetention ()

precisionRefinementDoesNotPromoteHistoryChange :
  PrecisionRefinementPromotesHistoryChange → ⊥
precisionRefinementDoesNotPromoteHistoryChange ()

precisionDepthDoesNotPromotePAdicValuation :
  PrecisionDepthPromotesPAdicValuation → ⊥
precisionDepthDoesNotPromotePAdicValuation ()

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionObservationPrecisionRefinementBoundary : Set where
  constructor intellectual-reception-observation-precision-refinement-boundary
  field
    precisionSelectorIsExplicit : Bool
    refinementPreservesAllPreviouslySelectedCoordinates : Bool
    finerAgreementImpliesCoarserAgreement : Bool
    coarseAgreementImpliesFinerAgreement : Bool
    projectedSupportDependsOnPrecision : Bool
    coarseProjectedAuthoritySupportCanBeRetained : Bool
    fineProjectionCanExposeDivergentAuthority : Bool
    newlyExposedDivergenceCanReopenDownstream : Bool
    projectedRetentionMeansFullSupportRetention : Bool
    precisionRefinementChangesUnderlyingHistory : Bool
    precisionIsLiteralPAdicValuation : Bool
    sourceAttributionBoundarySurvivesPrecisionRefinement : Bool

canonicalIntellectualReceptionObservationPrecisionRefinementBoundary :
  IntellectualReceptionObservationPrecisionRefinementBoundary
canonicalIntellectualReceptionObservationPrecisionRefinementBoundary =
  intellectual-reception-observation-precision-refinement-boundary
    true true true false true true true true false false false true
