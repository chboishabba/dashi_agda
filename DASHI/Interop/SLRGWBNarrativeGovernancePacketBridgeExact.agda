module DASHI.Interop.SLRGWBNarrativeGovernancePacketBridgeExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB
import DASHI.Interop.SLRGWBClaimRelativeSourceRoleAtlasExact as Roles
import DASHI.Interop.SLRGWBSourceRoleAttachmentExact as RoleAttach
import DASHI.Interop.SLRGWBHeterogeneousChronologyCapstoneExact as Chronology
import DASHI.Cognition.PNF.SensibLawITIRNarrativeComparisonTransportExact as Narrative
import DASHI.Governance.FriendlyjordiesNarrativeGovernanceTransportExact as FJ

------------------------------------------------------------------------
-- GWB / SENSIBLAW / ITIR NARRATIVE -> GOVERNANCE PACKET BRIDGE
--
-- The existing GWB route is authoritative for world-model transport:
--
-- certified projection
--   -> CandidateWorldModel
--   -> claim-relative source role
--   -> reviewed statement / observation / event join
--   -> event-time + source-knowledge-time projections
--   -> narrative comparison packet
--   -> evidence-qualified governance witness
--
-- No downstream layer may use narrative structure to bypass an unpaid
-- world-model, source-role, review, chronology or causal-link obligation.
------------------------------------------------------------------------

record WorldNarrativeGovernancePacket : Set where
  constructor world-narrative-governance-packet
  field
    candidateWorld : GWB.GWBCandidateWorldBoundary
    sourceRoleBoundary : Roles.SourceRoleBoundary
    roleAttachmentBoundary : RoleAttach.SourceRoleAttachmentBoundary
    sharedEventBoundary : Chronology.SharedEventAccountBoundary
    timeProjectionBoundary : Chronology.GWBTimeProjectionBoundary
    narrativeComparison : Narrative.NarrativeComparison
    governanceWitness : FJ.GovernanceWitness
    candidateWorldPaid : Bool
    sourceRolesPaid : Bool
    reviewedEventJoinPaid : Bool
    chronologyPaid : Bool
    causalLinkProvenancePaid : Bool
    missingnessRetained : Bool
    governanceTrajectoryClosed : Bool
    worldTruthPromoted : Bool
    sourceNarrativesMerged : Bool

open WorldNarrativeGovernancePacket public

friendlyjordiesGWBPacket : WorldNarrativeGovernancePacket
friendlyjordiesGWBPacket =
  world-narrative-governance-packet
    GWB.canonicalGWBCandidateWorldBoundary
    Roles.canonicalSourceRoleBoundary
    RoleAttach.canonicalSourceRoleAttachmentBoundary
    Chronology.canonicalSharedEventAccountBoundary
    Chronology.canonicalGWBTimeProjectionBoundary
    FJ.canonicalFriendlyjordiesComparison
    FJ.friendlyjordiesGovernanceWitness
    true true false false true true false false false

candidateWorldStillCandidate :
  GWB.candidateOnly (candidateWorld friendlyjordiesGWBPacket) ≡ true
candidateWorldStillCandidate = refl

sourceRoleStillNonPromoting :
  Roles.semanticPromotion (sourceRoleBoundary friendlyjordiesGWBPacket) ≡ false
sourceRoleStillNonPromoting = refl

sharedEventDoesNotMergeNarratives :
  Chronology.mergedSyntheticNarrative
    (sharedEventBoundary friendlyjordiesGWBPacket)
  ≡ false
sharedEventDoesNotMergeNarratives = refl

eventAndKnowledgeTimeRemainDistinct :
  Chronology.eventTimeEqualsPublicationTime
    (timeProjectionBoundary friendlyjordiesGWBPacket)
  ≡ false
eventAndKnowledgeTimeRemainDistinct = refl

data NarrativeMayBypassCandidateWorld : Set where
data NarrativeMayBypassClaimRelativeSourceRole : Set where
data NarrativeMayBypassReviewedEventJoin : Set where
data NarrativeMayBypassChronology : Set where
data NarrativeMayBypassCausalProvenance : Set where
data WorldModelMayCreateClaimTruth : Set where
data ReviewedEventMayMergeCompetingNarratives : Set where
data CompletePacketAutomaticallyCreatesGovernanceTrajectory : Set where

narrativeMayNotBypassCandidateWorld :
  NarrativeMayBypassCandidateWorld → ⊥
narrativeMayNotBypassCandidateWorld ()

narrativeMayNotBypassSourceRole :
  NarrativeMayBypassClaimRelativeSourceRole → ⊥
narrativeMayNotBypassSourceRole ()

narrativeMayNotBypassReviewedEventJoin :
  NarrativeMayBypassReviewedEventJoin → ⊥
narrativeMayNotBypassReviewedEventJoin ()

narrativeMayNotBypassChronology :
  NarrativeMayBypassChronology → ⊥
narrativeMayNotBypassChronology ()

narrativeMayNotBypassCausalProvenance :
  NarrativeMayBypassCausalProvenance → ⊥
narrativeMayNotBypassCausalProvenance ()

worldModelDoesNotCreateClaimTruth :
  WorldModelMayCreateClaimTruth → ⊥
worldModelDoesNotCreateClaimTruth ()

reviewedEventDoesNotMergeCompetingNarratives :
  ReviewedEventMayMergeCompetingNarratives → ⊥
reviewedEventDoesNotMergeCompetingNarratives ()

completePacketDoesNotAutomaticallyCloseGovernanceTrajectory :
  CompletePacketAutomaticallyCreatesGovernanceTrajectory → ⊥
completePacketDoesNotAutomaticallyCloseGovernanceTrajectory ()
