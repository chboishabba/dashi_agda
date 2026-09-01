module DASHI.Governance.ReceptionEvidenceSelectiveReopeningExact where

------------------------------------------------------------------------
-- RECEPTION-EVIDENCE SELECTIVE REOPENING
--
-- New source evidence should reopen exactly the downstream reception claims
-- whose dependency paths consume it.  A stale historical/genealogical claim is
-- reopenable rather than automatically refuted, and an evidence-strength update
-- does not silently rewrite the claimed relation kind.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Governance.ReceptionRelationEvidenceTemporalGraphExact as Graph

------------------------------------------------------------------------
-- 1. Audit artifacts and reverse-dependency graph.
------------------------------------------------------------------------

data ReceptionAuditArtifact : Set where
  sourceReceiptArtifact
  edgeClassificationArtifact
  semanticTransportArtifact
  institutionalContinuityArtifact
  presentUseArtifact
  downstreamPolicyArtifact
  : ReceptionAuditArtifact

data ReceptionDepends : ReceptionAuditArtifact → ReceptionAuditArtifact → Set where
  sourceToEdge : ReceptionDepends sourceReceiptArtifact edgeClassificationArtifact
  edgeToSemantic : ReceptionDepends edgeClassificationArtifact semanticTransportArtifact
  edgeToInstitution : ReceptionDepends edgeClassificationArtifact institutionalContinuityArtifact
  semanticToPresent : ReceptionDepends semanticTransportArtifact presentUseArtifact
  institutionToPresent : ReceptionDepends institutionalContinuityArtifact presentUseArtifact
  presentToPolicy : ReceptionDepends presentUseArtifact downstreamPolicyArtifact

------------------------------------------------------------------------
-- 2. Concrete reopening obligations.
------------------------------------------------------------------------

edgeChangeReopensSemantic :
  Dependency.ReopeningObligation
    ReceptionDepends edgeClassificationArtifact semanticTransportArtifact
edgeChangeReopensSemantic = Dependency.oneEdgeCreatesReopeningObligation edgeToSemantic

edgeChangeReopensInstitution :
  Dependency.ReopeningObligation
    ReceptionDepends edgeClassificationArtifact institutionalContinuityArtifact
edgeChangeReopensInstitution = Dependency.oneEdgeCreatesReopeningObligation edgeToInstitution

edgeChangeReopensPresentUse :
  Dependency.ReopeningObligation
    ReceptionDepends edgeClassificationArtifact presentUseArtifact
edgeChangeReopensPresentUse =
  Dependency.obligationsCompose
    edgeChangeReopensSemantic
    (Dependency.oneEdgeCreatesReopeningObligation semanticToPresent)

edgeChangeReopensPolicyTransitively :
  Dependency.ReopeningObligation
    ReceptionDepends edgeClassificationArtifact downstreamPolicyArtifact
edgeChangeReopensPolicyTransitively =
  Dependency.obligationsCompose
    edgeChangeReopensPresentUse
    (Dependency.oneEdgeCreatesReopeningObligation presentToPolicy)

sourceChangeReopensPolicyTransitively :
  Dependency.ReopeningObligation
    ReceptionDepends sourceReceiptArtifact downstreamPolicyArtifact
sourceChangeReopensPolicyTransitively =
  Dependency.obligationsCompose
    (Dependency.oneEdgeCreatesReopeningObligation sourceToEdge)
    edgeChangeReopensPolicyTransitively

------------------------------------------------------------------------
-- 3. Strength update and relation reclassification are distinct operations.
------------------------------------------------------------------------

data EvidenceUpdateKind : Set where
  strengthOnlyUpdate
  relationReclassificationUpdate
  : EvidenceUpdateKind

record RelationReclassificationReceipt : Set where
  constructor relation-reclassification-receipt
  field
    oldKind : Graph.ReceptionRelationKind
    newKind : Graph.ReceptionRelationKind
    sourceSpecificEvidenceLocated : Bool
    temporalRouteChecked : Bool
    semanticRouteChecked : Bool
    boundedReason : String
open RelationReclassificationReceipt public

data StrengthOnlyUpdateRewritesRelationKind : Set where

data StaleClaimAutomaticallyRefuted : Set where

data EveryHistoricalClaimMustReopen : Set where

strengthOnlyUpdateDoesNotRewriteRelationKind :
  StrengthOnlyUpdateRewritesRelationKind → ⊥
strengthOnlyUpdateDoesNotRewriteRelationKind ()

staleClaimIsNotAutomaticallyRefuted : StaleClaimAutomaticallyRefuted → ⊥
staleClaimIsNotAutomaticallyRefuted ()

noGlobalReopeningWithoutDependencyPath : EveryHistoricalClaimMustReopen → ⊥
noGlobalReopeningWithoutDependencyPath ()

------------------------------------------------------------------------
-- 4. A finite reclassification specimen.
--
-- New archival evidence may justify changing a previously circumstantial
-- lexical-borrowing edge to direct citation, but only through an explicit
-- reclassification receipt.  The generic evidence-strength coordinate itself
-- does not perform that rewrite.
------------------------------------------------------------------------

archivalCitationReclassification : RelationReclassificationReceipt
archivalCitationReclassification =
  relation-reclassification-receipt
    Graph.lexicalBorrowing
    Graph.directCitation
    true true true
    "finite DASHI specimen: a newly recovered explicit citation can justify relation reclassification after source, temporal and semantic checks"

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record ReceptionSelectiveReopeningBoundary : Set where
  constructor reception-selective-reopening-boundary
  field
    sourceChangeMayReopenDownstreamTransitively : Bool
    edgeReclassificationMayReopenMeaningAndInstitutionClaims : Bool
    evidenceStrengthAloneRewritesRelationKind : Bool
    staleClaimEqualsRefutedClaim : Bool
    allHistoricalClaimsReopenAfterEverySourceChange : Bool
    dependencyPathRequiredForSelectiveReopening : Bool

canonicalReceptionSelectiveReopeningBoundary : ReceptionSelectiveReopeningBoundary
canonicalReceptionSelectiveReopeningBoundary =
  reception-selective-reopening-boundary true true false false false true
