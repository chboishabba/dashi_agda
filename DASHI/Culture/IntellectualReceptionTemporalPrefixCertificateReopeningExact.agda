module DASHI.Culture.IntellectualReceptionTemporalPrefixCertificateReopeningExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / TEMPORAL PREFIX-LOCAL CERTIFICATE REOPENING
--
-- Certificates at an intermediate time are justified by the exact path prefix
-- ending at that time.  A later edge that is not structurally present in that
-- prefix cannot supply the membership premise required by the dependency
-- constructor.  Prefix extension preserves all earlier edge occurrences.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Culture.IntellectualReceptionComposableFibreTransportPathExact as Paths
import DASHI.Culture.IntellectualReceptionStructuralFibreTransportReopeningExact as Structural
import DASHI.Culture.IntellectualReceptionPathIndexedCertificateDependencyExact as PathDependency
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal

------------------------------------------------------------------------
-- 1. A prefix is an exact path together with a suffix decomposition receipt.
------------------------------------------------------------------------

record PathPrefix
    {history : Temporal.TemporalReceptionHistory}
    {start middle finish : Temporal.ReceptionTime}
    (prefix : Paths.FibreTransportPath history start middle)
    (whole : Paths.FibreTransportPath history start finish) : Set where
  constructor path-prefix
  field
    suffix : Paths.FibreTransportPath history middle finish
    wholeIsAppend : Paths.appendPath prefix suffix ≡ whole

open PathPrefix public

earlyPrefix01Of02 :
  PathPrefix Paths.earlyAuthorityPath01 Paths.earlyAuthorityPath02
earlyPrefix01Of02 =
  path-prefix Paths.earlyAuthorityPath12 refl

latePrefix01Of02 :
  PathPrefix Paths.lateAuthorityPath01 Paths.lateAuthorityPath02
latePrefix01Of02 =
  path-prefix Paths.lateAuthorityPath12 refl

------------------------------------------------------------------------
-- 2. Earlier edge membership survives extension to a later prefix/whole path.
------------------------------------------------------------------------

earlyAcquireOccursAtT1Prefix :
  Structural.EdgeOccurs
    Structural.EarlyAcquireEdge
    Paths.earlyAuthorityPath01
earlyAcquireOccursAtT1Prefix = Structural.earlyAcquireOccursInPrefix

earlyAcquireOccurrenceSurvivesToT2 :
  Structural.EdgeOccurs
    Structural.EarlyAcquireEdge
    Paths.earlyAuthorityPath02
earlyAcquireOccurrenceSurvivesToT2 =
  Structural.occursInLeftAfterAppend earlyAcquireOccursAtT1Prefix

------------------------------------------------------------------------
-- 3. A later acquisition edge is absent from the earlier t1 prefix.
------------------------------------------------------------------------

lateAcquireNotInT1Prefix :
  Structural.EdgeOccurs
    Structural.LateAcquireEdge
    Paths.lateAuthorityPath01 → ⊥
lateAcquireNotInT1Prefix ()

lateAcquireOccursAtT2Whole :
  Structural.EdgeOccurs
    Structural.LateAcquireEdge
    Paths.lateAuthorityPath02
lateAcquireOccursAtT2Whole = Structural.lateAcquireOccursInComposedPath

------------------------------------------------------------------------
-- 4. Certificates are generated from the exact prefix ending at their time.
------------------------------------------------------------------------

module EarlyT1Certificate =
  PathDependency.PathIndexedCertificateDependency
    Structural.EarlyAcquireEdge
    Paths.earlyAuthorityPath01

module EarlyT2Certificate =
  PathDependency.PathIndexedCertificateDependency
    Structural.EarlyAcquireEdge
    Paths.earlyAuthorityPath02

module LateT1Certificate =
  PathDependency.PathIndexedCertificateDependency
    Structural.LateAcquireEdge
    Paths.lateAuthorityPath01

module LateT2Certificate =
  PathDependency.PathIndexedCertificateDependency
    Structural.LateAcquireEdge
    Paths.lateAuthorityPath02

earlyAcquireReopensT1PrefixCertificate :
  Affected.ReopeningObligation
    EarlyT1Certificate.Depends
    EarlyT1Certificate.edgeArtifact
    EarlyT1Certificate.pathCertificate
earlyAcquireReopensT1PrefixCertificate =
  EarlyT1Certificate.membershipCreatesPathReopening
    earlyAcquireOccursAtT1Prefix

earlyAcquireReopensT2PrefixCertificate :
  Affected.ReopeningObligation
    EarlyT2Certificate.Depends
    EarlyT2Certificate.edgeArtifact
    EarlyT2Certificate.pathCertificate
earlyAcquireReopensT2PrefixCertificate =
  EarlyT2Certificate.membershipCreatesPathReopening
    earlyAcquireOccurrenceSurvivesToT2

lateAcquireReopensT2PrefixCertificate :
  Affected.ReopeningObligation
    LateT2Certificate.Depends
    LateT2Certificate.edgeArtifact
    LateT2Certificate.pathCertificate
lateAcquireReopensT2PrefixCertificate =
  LateT2Certificate.membershipCreatesPathReopening
    lateAcquireOccursAtT2Whole

------------------------------------------------------------------------
-- 5. The unavailable t1 membership premise blocks path-local reopening there.
------------------------------------------------------------------------

lateT1MembershipWouldContradictPrefixStructure :
  Structural.EdgeOccurs
    Structural.LateAcquireEdge
    Paths.lateAuthorityPath01 → ⊥
lateT1MembershipWouldContradictPrefixStructure = lateAcquireNotInT1Prefix

-- We state the boundary at the membership premise rather than postulating a
-- global negation of every possible dependency closure.  The generic dependency
-- constructor requires exactly this premise, and there is no such witness.

data LaterEdgePromotesEarlierPrefixMembership : Set where

laterEdgeDoesNotPromoteEarlierPrefixMembership :
  LaterEdgePromotesEarlierPrefixMembership → ⊥
laterEdgeDoesNotPromoteEarlierPrefixMembership ()

------------------------------------------------------------------------
-- 6. Prefix refinement is monotone for already-witnessed path incidence.
------------------------------------------------------------------------

record PrefixIncidenceMonotonicity : Set where
  constructor prefix-incidence-monotonicity
  field
    earlyOccurrenceAtT1 :
      Structural.EdgeOccurs
        Structural.EarlyAcquireEdge
        Paths.earlyAuthorityPath01
    earlyOccurrenceAtT2 :
      Structural.EdgeOccurs
        Structural.EarlyAcquireEdge
        Paths.earlyAuthorityPath02

canonicalPrefixIncidenceMonotonicity : PrefixIncidenceMonotonicity
canonicalPrefixIncidenceMonotonicity =
  prefix-incidence-monotonicity
    earlyAcquireOccursAtT1Prefix
    earlyAcquireOccurrenceSurvivesToT2

------------------------------------------------------------------------
-- 7. No-promotion boundaries.
------------------------------------------------------------------------

data PrefixLocalityPromotesPAdicIdentity : Set where
data PrefixLocalityPromotesFloatingPointEquality : Set where
data PrefixCertificatePromotesActualChronology : Set where

aPrefixLocalityDoesNotPromotePAdicIdentity :
  PrefixLocalityPromotesPAdicIdentity → ⊥
aPrefixLocalityDoesNotPromotePAdicIdentity ()

prefixLocalityDoesNotPromoteFloatingPointEquality :
  PrefixLocalityPromotesFloatingPointEquality → ⊥
prefixLocalityDoesNotPromoteFloatingPointEquality ()

prefixCertificateDoesNotPromoteActualChronology :
  PrefixCertificatePromotesActualChronology → ⊥
prefixCertificateDoesNotPromoteActualChronology ()

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionTemporalPrefixCertificateReopeningBoundary : Set where
  constructor intellectual-reception-temporal-prefix-certificate-reopening-boundary
  field
    certificateIsIndexedByExactTemporalPrefix : Bool
    existingEdgeMembershipSurvivesPrefixExtension : Bool
    laterNonmemberEdgeCreatesEarlierMembership : Bool
    prefixMembershipCanCreateSelectiveReopening : Bool
    prefixLocalityIsLiteralPAdicIdentity : Bool
    prefixLocalityIsFloatingPointEquality : Bool
    sourceAttributionBoundarySurvivesPrefixReopening : Bool

canonicalIntellectualReceptionTemporalPrefixCertificateReopeningBoundary :
  IntellectualReceptionTemporalPrefixCertificateReopeningBoundary
canonicalIntellectualReceptionTemporalPrefixCertificateReopeningBoundary =
  intellectual-reception-temporal-prefix-certificate-reopening-boundary
    true true false true false false true
