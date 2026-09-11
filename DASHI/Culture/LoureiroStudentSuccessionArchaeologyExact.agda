module DASHI.Culture.LoureiroStudentSuccessionArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LOUREIRO STUDENT SUCCESSION ARCHAEOLOGY
--
-- Thin source/succession ledger.  Existing scientific and succession owners
-- remain authoritative.  This owner distinguishes coauthored scientific work,
-- current group membership, temporary/external PhD supervision, and formal
-- advisor-of-record succession so those relations cannot be collapsed.
------------------------------------------------------------------------

record StudentSuccessionCarrier : Set where
  constructor student-succession-carrier
  field
    student : String
    carrierObject : String
    stableIdentifier : String
    sourceLink : String
    sourceClass : String
    relationshipPaid : String
    qidCoordinate : String
    qidVerified : Bool
    deweyTraversal : String
    formalAdvisorReassignmentPaid : Bool
    grantTransferPaid : Bool
    repositoryTransferPaid : Bool

open StudentSuccessionCarrier public

simranLoureiroPaper : StudentSuccessionCarrier
simranLoureiroPaper = student-succession-carrier
  "Simran Chowdhry"
  "Current sheet formation under radiative cooling — Simran Chowdhry; Nuno F. Loureiro"
  "DOI 10.1017/S0022377825100949"
  "https://doi.org/10.1017/S0022377825100949"
  "primary peer-reviewed publication"
  "pre-loss Loureiro coauthorship/advising lineage; corresponding author Simran Chowdhry"
  "unresolvedQid"
  false
  "530 Physics"
  false false false

simranCurrentMITGroupCarrier : StudentSuccessionCarrier
simranCurrentMITGroupCarrier = student-succession-carrier
  "Simran Chowdhry"
  "MIT PUFFIN current team page"
  "primary institutional team page; no DOI"
  "https://puffin.mit.edu/team/"
  "primary institutional group page"
  "current page describes Simran as jointly working with Jack Hare and Nuno Loureiro"
  "unresolvedQid"
  false
  "530 Physics"
  false false false

simranOxford2026Carrier : StudentSuccessionCarrier
simranOxford2026Carrier = student-succession-carrier
  "Simran Chowdhry"
  "Oxford plasma-group Autumn/Michaelmas 2026 visitor/work plan"
  "primary institutional schedule; no DOI"
  "https://www-thphys.physics.ox.ac.uk/research/plasma/seminarsM26.html"
  "primary institutional programme page"
  "states Simran moves to Oxford for a term to work on her PhD with Dmitri Uzdensky"
  "unresolvedQid"
  false
  "530 Physics"
  false false false

------------------------------------------------------------------------
-- Named research-supervision transition state.
------------------------------------------------------------------------

record StudentSupervisionTransition : Set where
  constructor student-supervision-transition
  field
    student : String
    priorAdvisor : String
    priorAdvisorRelationPrimaryPaid : Bool
    continuingMITCollaborator : String
    external2026ResearchSupervisor : String
    postLossResearchSupervisionLocated : Bool
    formalMITAdvisorOfRecordLocated : Bool
    temporaryVisitEqualsFormalAdvisorReassignment : Bool
    currentGroupPageWithDeceasedAdvisorEqualsCurrentFormalState : Bool
    acquisitionTarget : String

open StudentSupervisionTransition public

simranPostLossSupervisionTransition : StudentSupervisionTransition
simranPostLossSupervisionTransition = student-supervision-transition
  "Simran Chowdhry"
  "Nuno F. Loureiro"
  true
  "Jack D. Hare"
  "Dmitri Uzdensky"
  true
  false
  false
  false
  "MIT advisor-of-record / thesis committee / graduate programme record after 2025-12-16; distinguish temporary Oxford research supervision from formal MIT advisor reassignment"

------------------------------------------------------------------------
-- Attribution and promotion firewalls.
------------------------------------------------------------------------

record StudentSuccessionBoundary : Set where
  constructor student-succession-boundary
  field
    doiCreatesAdvisorSuccession : Bool
    currentTeamPageCreatesFormalAdvisorState : Bool
    externalResearchSupervisionCreatesGrantTransfer : Bool
    temporaryVisitCreatesRepositoryTransfer : Bool
    postLossResearchSupervisionMayGuideAdvisorSearch : Bool
    unresolvedQidMayBeGuessedFromName : Bool
    deweyCreatesRelationshipAuthority : Bool

open StudentSuccessionBoundary public

canonicalStudentSuccessionBoundary : StudentSuccessionBoundary
canonicalStudentSuccessionBoundary = student-succession-boundary
  false false false false true false false
