module DASHI.Culture.IntellectualReceptionStructuralFibreTransportReopeningExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / STRUCTURAL FIBRE-PATH MEMBERSHIP + REOPENING
--
-- Edge occurrence is derived structurally from FibreTransportPath itself.
-- No route-level occurrence enumeration is needed.  An edge predicate is
-- proof-relevant and indexed by the actual FibreTransport receipt.
--
-- Membership survives path concatenation on either side, and downstream
-- reopening is generated directly from a structural membership witness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact as Paths
import DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreTransportExact as Transport
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal

------------------------------------------------------------------------
-- 1. Edge properties and structural occurrence in an indexed path.
------------------------------------------------------------------------

EdgeProperty :
  (history : Temporal.TemporalReceptionHistory) → Set₁
EdgeProperty history =
  ∀ {from to} → Transport.FibreTransport history from to → Set

data EdgeOccurs
    {history : Temporal.TemporalReceptionHistory}
    (P : EdgeProperty history) :
    ∀ {start finish} →
    Paths.FibreTransportPath history start finish → Set where

  occursHere :
    ∀ {start middle finish}
      {edge : Transport.FibreTransport history start middle}
      {rest : Paths.FibreTransportPath history middle finish} →
    P edge →
    EdgeOccurs P (Paths.pathStep edge rest)

  occursLater :
    ∀ {start middle finish}
      {edge : Transport.FibreTransport history start middle}
      {rest : Paths.FibreTransportPath history middle finish} →
    EdgeOccurs P rest →
    EdgeOccurs P (Paths.pathStep edge rest)

------------------------------------------------------------------------
-- 2. Structural membership is stable under append.
------------------------------------------------------------------------

occursInLeftAfterAppend :
  ∀ {history start middle finish}
    {P : EdgeProperty history}
    {left : Paths.FibreTransportPath history start middle}
    {right : Paths.FibreTransportPath history middle finish} →
  EdgeOccurs P left →
  EdgeOccurs P (Paths.appendPath left right)
occursInLeftAfterAppend {left = Paths.pathRefl} ()
occursInLeftAfterAppend {left = Paths.pathStep edge rest} (occursHere proof) =
  occursHere proof
occursInLeftAfterAppend {left = Paths.pathStep edge rest} (occursLater proof) =
  occursLater (occursInLeftAfterAppend proof)

occursInRightAfterAppend :
  ∀ {history start middle finish}
    {P : EdgeProperty history}
    {left : Paths.FibreTransportPath history start middle}
    {right : Paths.FibreTransportPath history middle finish} →
  EdgeOccurs P right →
  EdgeOccurs P (Paths.appendPath left right)
occursInRightAfterAppend {left = Paths.pathRefl} proof = proof
occursInRightAfterAppend {left = Paths.pathStep edge rest} proof =
  occursLater (occursInRightAfterAppend {left = rest} proof)

------------------------------------------------------------------------
-- 3. Exact edge-instance predicates for the two authority histories.
------------------------------------------------------------------------

data EarlyAcquireEdge :
  ∀ {from to} →
  Transport.FibreTransport
    Temporal.movementEarlyAuthorityHistory from to → Set where

  earlyAcquire01 :
    EarlyAcquireEdge
      (Transport.transport01 Temporal.movementEarlyAuthorityHistory)

data LateAcquireEdge :
  ∀ {from to} →
  Transport.FibreTransport
    Temporal.movementLateAuthorityHistory from to → Set where

  lateAcquire12 :
    LateAcquireEdge
      (Transport.transport12 Temporal.movementLateAuthorityHistory)

------------------------------------------------------------------------
-- 4. Membership is obtained from the actual path constructors.
------------------------------------------------------------------------

earlyAcquireOccursInPrefix :
  EdgeOccurs EarlyAcquireEdge Paths.earlyAuthorityPath01
earlyAcquireOccursInPrefix = occursHere earlyAcquire01

earlyAcquireOccursInComposedPath :
  EdgeOccurs EarlyAcquireEdge Paths.earlyAuthorityPath02
earlyAcquireOccursInComposedPath =
  occursInLeftAfterAppend earlyAcquireOccursInPrefix

lateAcquireOccursInSuffix :
  EdgeOccurs LateAcquireEdge Paths.lateAuthorityPath12
lateAcquireOccursInSuffix = occursHere lateAcquire12

lateAcquireOccursInComposedPath :
  EdgeOccurs LateAcquireEdge Paths.lateAuthorityPath02
lateAcquireOccursInComposedPath =
  occursInRightAfterAppend lateAcquireOccursInSuffix

------------------------------------------------------------------------
-- 5. Certificates are indexed by the path whose structure justified them.
------------------------------------------------------------------------

data StructuralFibreCertificateArtifact : Set where
  earlyAcquireEdgeArtifact
  lateAcquireEdgeArtifact
  earlyPathCertificate
  latePathCertificate
  earlyFutureCertificate
  lateFutureCertificate
  : StructuralFibreCertificateArtifact

data StructuralDepends :
  StructuralFibreCertificateArtifact →
  StructuralFibreCertificateArtifact → Set where

  earlyMembershipCreatesDependency :
    EdgeOccurs EarlyAcquireEdge Paths.earlyAuthorityPath02 →
    StructuralDepends earlyAcquireEdgeArtifact earlyPathCertificate

  lateMembershipCreatesDependency :
    EdgeOccurs LateAcquireEdge Paths.lateAuthorityPath02 →
    StructuralDepends lateAcquireEdgeArtifact latePathCertificate

  earlyPathFeedsFuture :
    StructuralDepends earlyPathCertificate earlyFutureCertificate

  latePathFeedsFuture :
    StructuralDepends latePathCertificate lateFutureCertificate

------------------------------------------------------------------------
-- 6. Reopening is now generated directly from structural membership.
------------------------------------------------------------------------

earlyStructuralMembershipReopensPathCertificate :
  Affected.ReopeningObligation
    StructuralDepends
    earlyAcquireEdgeArtifact
    earlyPathCertificate
earlyStructuralMembershipReopensPathCertificate =
  Affected.oneEdgeCreatesReopeningObligation
    (earlyMembershipCreatesDependency earlyAcquireOccursInComposedPath)

lateStructuralMembershipReopensPathCertificate :
  Affected.ReopeningObligation
    StructuralDepends
    lateAcquireEdgeArtifact
    latePathCertificate
lateStructuralMembershipReopensPathCertificate =
  Affected.oneEdgeCreatesReopeningObligation
    (lateMembershipCreatesDependency lateAcquireOccursInComposedPath)

earlyPathReopensFuture :
  Affected.ReopeningObligation
    StructuralDepends
    earlyPathCertificate
    earlyFutureCertificate
earlyPathReopensFuture =
  Affected.oneEdgeCreatesReopeningObligation earlyPathFeedsFuture

latePathReopensFuture :
  Affected.ReopeningObligation
    StructuralDepends
    latePathCertificate
    lateFutureCertificate
latePathReopensFuture =
  Affected.oneEdgeCreatesReopeningObligation latePathFeedsFuture

earlyStructuralMembershipReopensFuture :
  Affected.ReopeningObligation
    StructuralDepends
    earlyAcquireEdgeArtifact
    earlyFutureCertificate
earlyStructuralMembershipReopensFuture =
  Affected.obligationsCompose
    earlyStructuralMembershipReopensPathCertificate
    earlyPathReopensFuture

lateStructuralMembershipReopensFuture :
  Affected.ReopeningObligation
    StructuralDepends
    lateAcquireEdgeArtifact
    lateFutureCertificate
lateStructuralMembershipReopensFuture =
  Affected.obligationsCompose
    lateStructuralMembershipReopensPathCertificate
    latePathReopensFuture

------------------------------------------------------------------------
-- 7. Exact edge predicates prevent route-kind collapse.
------------------------------------------------------------------------

-- There is no way to use an EarlyAcquireEdge witness as a LateAcquireEdge
-- witness: they are indexed over different history-specific FibreTransport
-- carriers.  Cross-route dependencies consequently have no constructors.

earlyEdgeDoesNotDirectlyDependOnLatePath :
  StructuralDepends earlyAcquireEdgeArtifact latePathCertificate → ⊥
earlyEdgeDoesNotDirectlyDependOnLatePath ()

lateEdgeDoesNotDirectlyDependOnEarlyPath :
  StructuralDepends lateAcquireEdgeArtifact earlyPathCertificate → ⊥
lateEdgeDoesNotDirectlyDependOnEarlyPath ()

------------------------------------------------------------------------
-- 8. No-promotion boundaries.
------------------------------------------------------------------------

data StructuralMembershipPromotesCausalNecessity : Set where
data StructuralReopeningPromotesRefutation : Set where
data PathAppendPromotesHistoricalContinuity : Set where

structuralMembershipDoesNotPromoteCausalNecessity :
  StructuralMembershipPromotesCausalNecessity → ⊥
structuralMembershipDoesNotPromoteCausalNecessity ()

structuralReopeningDoesNotPromoteRefutation :
  StructuralReopeningPromotesRefutation → ⊥
structuralReopeningDoesNotPromoteRefutation ()

pathAppendDoesNotPromoteHistoricalContinuity :
  PathAppendPromotesHistoricalContinuity → ⊥
pathAppendDoesNotPromoteHistoricalContinuity ()

------------------------------------------------------------------------
-- 9. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionStructuralFibreTransportReopeningBoundary : Set where
  constructor intellectual-reception-structural-fibre-transport-reopening-boundary
  field
    edgeOccurrenceIsStructuralOverPath : Bool
    leftMembershipSurvivesAppend : Bool
    rightMembershipSurvivesAppend : Bool
    reopeningConsumesStructuralMembership : Bool
    reopeningPropagatesTransitively : Bool
    crossRouteDependencyIsManufacturedBySameEdgeKind : Bool
    reopeningMeansRefutation : Bool
    sourceAttributionBoundarySurvivesStructuralReopening : Bool

canonicalIntellectualReceptionStructuralFibreTransportReopeningBoundary :
  IntellectualReceptionStructuralFibreTransportReopeningBoundary
canonicalIntellectualReceptionStructuralFibreTransportReopeningBoundary =
  intellectual-reception-structural-fibre-transport-reopening-boundary
    true true true true true false false true
