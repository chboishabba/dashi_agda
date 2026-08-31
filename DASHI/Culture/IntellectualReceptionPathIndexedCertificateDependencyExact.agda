module DASHI.Culture.IntellectualReceptionPathIndexedCertificateDependencyExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / PATH-INDEXED CERTIFICATE DEPENDENCY
--
-- The dependency calculus is parameterized by an exact FibreTransportPath and
-- a proof-relevant edge predicate over that path's history.  A path certificate
-- is therefore tied to the path object that justified it; no early/late route
-- names are needed by the generic theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact as Paths
import DASHI.Culture.IntellectualReceptionStructuralFibreTransportReopeningExact as Structural
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal

------------------------------------------------------------------------
-- 1. Generic calculus indexed by one exact history/path and edge predicate.
------------------------------------------------------------------------

module PathIndexedCertificateDependency
    {history : Temporal.TemporalReceptionHistory}
    {start finish : Temporal.ReceptionTime}
    (P : Structural.EdgeProperty history)
    (path : Paths.FibreTransportPath history start finish)
    where

  data PathIndexedArtifact : Set where
    edgeArtifact
    pathCertificate
    futureCertificate
    : PathIndexedArtifact

  data Depends : PathIndexedArtifact → PathIndexedArtifact → Set where
    membershipCreatesPathDependency :
      Structural.EdgeOccurs P path →
      Depends edgeArtifact pathCertificate

    pathCertificateFeedsFuture :
      Depends pathCertificate futureCertificate

  membershipCreatesPathReopening :
    Structural.EdgeOccurs P path →
    Affected.ReopeningObligation
      Depends edgeArtifact pathCertificate
  membershipCreatesPathReopening occurrence =
    Affected.oneEdgeCreatesReopeningObligation
      (membershipCreatesPathDependency occurrence)

  pathReopensFuture :
    Affected.ReopeningObligation
      Depends pathCertificate futureCertificate
  pathReopensFuture =
    Affected.oneEdgeCreatesReopeningObligation pathCertificateFeedsFuture

  membershipCreatesFutureReopening :
    Structural.EdgeOccurs P path →
    Affected.ReopeningObligation
      Depends edgeArtifact futureCertificate
  membershipCreatesFutureReopening occurrence =
    Affected.obligationsCompose
      (membershipCreatesPathReopening occurrence)
      pathReopensFuture

------------------------------------------------------------------------
-- 2. Canonical early/late authority paths are now thin instantiations.
------------------------------------------------------------------------

module EarlyAuthorityDependency =
  PathIndexedCertificateDependency
    Structural.EarlyAcquireEdge
    Paths.earlyAuthorityPath02

module LateAuthorityDependency =
  PathIndexedCertificateDependency
    Structural.LateAcquireEdge
    Paths.lateAuthorityPath02

earlyAcquireReopensExactPathCertificate :
  Affected.ReopeningObligation
    EarlyAuthorityDependency.Depends
    EarlyAuthorityDependency.edgeArtifact
    EarlyAuthorityDependency.pathCertificate
earlyAcquireReopensExactPathCertificate =
  EarlyAuthorityDependency.membershipCreatesPathReopening
    Structural.earlyAcquireOccursInComposedPath

lateAcquireReopensExactPathCertificate :
  Affected.ReopeningObligation
    LateAuthorityDependency.Depends
    LateAuthorityDependency.edgeArtifact
    LateAuthorityDependency.pathCertificate
lateAcquireReopensExactPathCertificate =
  LateAuthorityDependency.membershipCreatesPathReopening
    Structural.lateAcquireOccursInComposedPath

earlyAcquireReopensExactFutureCertificate :
  Affected.ReopeningObligation
    EarlyAuthorityDependency.Depends
    EarlyAuthorityDependency.edgeArtifact
    EarlyAuthorityDependency.futureCertificate
earlyAcquireReopensExactFutureCertificate =
  EarlyAuthorityDependency.membershipCreatesFutureReopening
    Structural.earlyAcquireOccursInComposedPath

lateAcquireReopensExactFutureCertificate :
  Affected.ReopeningObligation
    LateAuthorityDependency.Depends
    LateAuthorityDependency.edgeArtifact
    LateAuthorityDependency.futureCertificate
lateAcquireReopensExactFutureCertificate =
  LateAuthorityDependency.membershipCreatesFutureReopening
    Structural.lateAcquireOccursInComposedPath

------------------------------------------------------------------------
-- 3. Path identity is part of the dependency type, not recoverable metadata.
------------------------------------------------------------------------

-- The early and late instantiations have different `Depends` types because the
-- exact path is a parameter of the module that generates each certificate
-- language.  There is no coercion from an early membership witness to a late
-- dependency constructor, or conversely.

data PathIndexedDependencyPromotesCrossPathCoercion : Set where

data PathCertificatePromotesActualHistory : Set where

data ReopeningPromotesRefutation : Set where

pathIndexedDependencyDoesNotPromoteCrossPathCoercion :
  PathIndexedDependencyPromotesCrossPathCoercion → ⊥
pathIndexedDependencyDoesNotPromoteCrossPathCoercion ()

pathCertificateDoesNotPromoteActualHistory :
  PathCertificatePromotesActualHistory → ⊥
pathCertificateDoesNotPromoteActualHistory ()

reopeningDoesNotPromoteRefutation :
  ReopeningPromotesRefutation → ⊥
reopeningDoesNotPromoteRefutation ()

------------------------------------------------------------------------
-- 4. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionPathIndexedCertificateDependencyBoundary : Set where
  constructor intellectual-reception-path-indexed-certificate-dependency-boundary
  field
    certificateLanguageIsIndexedByExactPath : Bool
    edgeMembershipConstructsPathDependency : Bool
    pathDependencyConstructsSelectiveReopening : Bool
    reopeningComposesToFutureCertificate : Bool
    crossPathDependencyCoercionIsAutomatic : Bool
    pathCertificateIsActualHistory : Bool
    reopeningMeansRefutation : Bool
    sourceAttributionBoundarySurvivesPathIndexedDependency : Bool

canonicalIntellectualReceptionPathIndexedCertificateDependencyBoundary :
  IntellectualReceptionPathIndexedCertificateDependencyBoundary
canonicalIntellectualReceptionPathIndexedCertificateDependencyBoundary =
  intellectual-reception-path-indexed-certificate-dependency-boundary
    true true true true false false false true
