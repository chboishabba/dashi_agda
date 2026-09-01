module DASHI.Culture.IntellectualReceptionSupportPartitionRetainReopenExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / SUPPORT PARTITION: RETAIN VS REOPEN
--
-- Retention and reopening are two outcomes of one support calculus.
-- Support wholly inside the shared observed prefix may be retained.  Support
-- containing a coordinate proved divergent at the chosen precision generates a
-- reopening obligation.  No conclusion is made merely from equal path length
-- or equal coarse endpoint display.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreExact as Fibre
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal

------------------------------------------------------------------------
-- 1. Divergence is coordinate-specific at the same t1 observation precision.
------------------------------------------------------------------------

data DivergentAtT1Precision : Reuse.PrefixCoordinate → Set where
  authorityDiverges : DivergentAtT1Precision Reuse.authorityCoordinate

presentNotDivergentAtT1 :
  DivergentAtT1Precision Reuse.presentCoordinate → ⊥
presentNotDivergentAtT1 ()

futureNotDivergentAtT1 :
  DivergentAtT1Precision Reuse.futureCoordinate → ⊥
futureNotDivergentAtT1 ()

authorityDifferenceReceipt :
  Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t1)
  ≡ Fibre.authorityEnabled
    (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t1) → ⊥
authorityDifferenceReceipt = Reuse.authorityReallyDiffersAtT1

------------------------------------------------------------------------
-- 2. A support intersects the divergent region only with a concrete witness.
------------------------------------------------------------------------

record SupportIntersectsDivergentRegion
    (support : Reuse.CertificateSupport) : Set where
  constructor support-intersects-divergent-region
  field
    coordinate : Reuse.PrefixCoordinate
    supported : Reuse.SupportedCoordinate support coordinate
    divergent : DivergentAtT1Precision coordinate

open SupportIntersectsDivergentRegion public

authoritySensitiveIntersectsDivergentRegion :
  SupportIntersectsDivergentRegion Reuse.authoritySensitiveSupport
authoritySensitiveIntersectsDivergentRegion =
  support-intersects-divergent-region
    Reuse.authorityCoordinate
    Reuse.supportAuthority
    authorityDiverges

presentFutureDoesNotIntersectDivergentRegion :
  SupportIntersectsDivergentRegion Reuse.presentFutureSupport → ⊥
presentFutureDoesNotIntersectDivergentRegion witness
  with coordinate witness | supported witness | divergent witness
... | Reuse.presentCoordinate | Reuse.supportPresent | divergence =
      presentNotDivergentAtT1 divergence
... | Reuse.futureCoordinate | Reuse.supportFuture | divergence =
      futureNotDivergentAtT1 divergence

------------------------------------------------------------------------
-- 3. Reopening is generated from divergent support via canonical closure.
------------------------------------------------------------------------

module DivergentSupportReopening (support : Reuse.CertificateSupport) where

  data Artifact : Set where
    divergentCoordinateArtifact
    supportCertificate
    downstreamCertificate
    : Artifact

  data Depends : Artifact → Artifact → Set where
    divergentSupportCreatesDependency :
      SupportIntersectsDivergentRegion support →
      Depends divergentCoordinateArtifact supportCertificate

    supportFeedsDownstream :
      Depends supportCertificate downstreamCertificate

  divergentSupportCreatesReopening :
    SupportIntersectsDivergentRegion support →
    Affected.ReopeningObligation
      Depends divergentCoordinateArtifact supportCertificate
  divergentSupportCreatesReopening intersection =
    Affected.oneEdgeCreatesReopeningObligation
      (divergentSupportCreatesDependency intersection)

  divergentSupportReopensDownstream :
    SupportIntersectsDivergentRegion support →
    Affected.ReopeningObligation
      Depends divergentCoordinateArtifact downstreamCertificate
  divergentSupportReopensDownstream intersection =
    Affected.obligationsCompose
      (divergentSupportCreatesReopening intersection)
      (Affected.oneEdgeCreatesReopeningObligation supportFeedsDownstream)

module AuthoritySensitiveReopening =
  DivergentSupportReopening Reuse.authoritySensitiveSupport

authoritySensitiveCertificateReopens :
  Affected.ReopeningObligation
    AuthoritySensitiveReopening.Depends
    AuthoritySensitiveReopening.divergentCoordinateArtifact
    AuthoritySensitiveReopening.supportCertificate
authoritySensitiveCertificateReopens =
  AuthoritySensitiveReopening.divergentSupportCreatesReopening
    authoritySensitiveIntersectsDivergentRegion

authoritySensitiveDownstreamReopens :
  Affected.ReopeningObligation
    AuthoritySensitiveReopening.Depends
    AuthoritySensitiveReopening.divergentCoordinateArtifact
    AuthoritySensitiveReopening.downstreamCertificate
authoritySensitiveDownstreamReopens =
  AuthoritySensitiveReopening.divergentSupportReopensDownstream
    authoritySensitiveIntersectsDivergentRegion

------------------------------------------------------------------------
-- 4. Retention and reopening are one support-indexed disposition calculus.
------------------------------------------------------------------------

data CertificateDisposition
    (support : Reuse.CertificateSupport) : Set where
  retain :
    Reuse.SupportContainedInSharedPrefix support →
    CertificateDisposition support

  reopen :
    SupportIntersectsDivergentRegion support →
    CertificateDisposition support

presentFutureDisposition :
  CertificateDisposition Reuse.presentFutureSupport
presentFutureDisposition = retain Reuse.presentFutureSupportContained

authoritySensitiveDisposition :
  CertificateDisposition Reuse.authoritySensitiveSupport
authoritySensitiveDisposition = reopen authoritySensitiveIntersectsDivergentRegion

retainIfSupportContained :
  ∀ {support} →
  Reuse.SupportContainedInSharedPrefix support →
  CertificateDisposition support
retainIfSupportContained = retain

reopenIfSupportIntersectsDivergence :
  ∀ {support} →
  SupportIntersectsDivergentRegion support →
  CertificateDisposition support
reopenIfSupportIntersectsDivergence = reopen

------------------------------------------------------------------------
-- 5. The two canonical supports cannot receive the opposite disposition.
------------------------------------------------------------------------

presentFutureCannotReopenFromThisDivergence :
  SupportIntersectsDivergentRegion Reuse.presentFutureSupport → ⊥
presentFutureCannotReopenFromThisDivergence =
  presentFutureDoesNotIntersectDivergentRegion

authoritySensitiveCannotRetainAtThisPrecision :
  Reuse.SupportContainedInSharedPrefix Reuse.authoritySensitiveSupport → ⊥
authoritySensitiveCannotRetainAtThisPrecision =
  Reuse.authoritySensitiveSupportNotContained

------------------------------------------------------------------------
-- 6. This is a support partition, not a truth/refutation partition.
------------------------------------------------------------------------

data RetentionPromotesFineHistoryEquality : Set where
data ReopeningPromotesRefutation : Set where
data DivergencePromotesCausalNecessity : Set where
data SupportPartitionPromotesPAdicIdentity : Set where

retentionDoesNotPromoteFineHistoryEquality :
  RetentionPromotesFineHistoryEquality → ⊥
retentionDoesNotPromoteFineHistoryEquality ()

reopeningDoesNotPromoteRefutation : ReopeningPromotesRefutation → ⊥
reopeningDoesNotPromoteRefutation ()

divergenceDoesNotPromoteCausalNecessity :
  DivergencePromotesCausalNecessity → ⊥
divergenceDoesNotPromoteCausalNecessity ()

supportPartitionDoesNotPromotePAdicIdentity :
  SupportPartitionPromotesPAdicIdentity → ⊥
supportPartitionDoesNotPromotePAdicIdentity ()

------------------------------------------------------------------------
-- 7. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionSupportPartitionRetainReopenBoundary : Set where
  constructor intellectual-reception-support-partition-retain-reopen-boundary
  field
    retainedSupportRequiresSharedContainment : Bool
    reopenedSupportRequiresDivergenceIntersection : Bool
    presentFutureSupportIsRetained : Bool
    authoritySensitiveSupportIsReopened : Bool
    divergentSupportCanReopenDownstreamClosure : Bool
    retentionMeansFineHistoryEquality : Bool
    reopeningMeansRefutation : Bool
    supportPartitionIsLiteralPAdicPartition : Bool
    sourceAttributionBoundarySurvivesSupportPartition : Bool

canonicalIntellectualReceptionSupportPartitionRetainReopenBoundary :
  IntellectualReceptionSupportPartitionRetainReopenBoundary
canonicalIntellectualReceptionSupportPartitionRetainReopenBoundary =
  intellectual-reception-support-partition-retain-reopen-boundary
    true true true true true false false false true
