module DASHI.Culture.LoureiroStudentSuccessionArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LOUREIRO STUDENT SUCCESSION ARCHAEOLOGY
--
-- Thin source/succession ledger. Existing scientific and succession owners
-- remain authoritative. This owner distinguishes coauthored scientific work,
-- current group membership, temporary/external PhD supervision, formal
-- advisor-of-record succession, and exact funding/compute-resource continuity.
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
-- Exact post-loss funding / compute-resource continuity.
--
-- The 2025 APS DPP abstract for the Li/Liu/Loureiro ion-acoustic project names
-- DOE DE-SC0022012, DOE DE-FG02-91-ER54109 and NERSC FES-ERCAP0026577.
-- Dion Li's genuinely post-loss solo APS Open Science article reuses exactly
-- DE-FG02-91ER54109 and FES-ERCAP0026577 (plus NSF GRFP 2141064), while not
-- naming DE-SC0022012. This pays continuity of specific infrastructure/resource
-- identifiers across the loss boundary, not transfer of a Loureiro-held grant,
-- PI authority, repository custody, or inherited simulation state.
------------------------------------------------------------------------

record ScientificResourceContinuityReceipt : Set where
  constructor scientific-resource-continuity-receipt
  field
    preLossObject : String
    preLossStableIdentifier : String
    preLossSourceLink : String
    preLossAwardSet : String
    postLossObject : String
    postLossStableIdentifier : String
    postLossSourceLink : String
    postLossAwardSet : String
    exactDOEInfrastructureAwardReused : Bool
    exactNERSCAllocationReused : Bool
    deSC0022012ReusedInPostLossObject : Bool
    postLossScientificResourceContinuityPaid : Bool
    formalGrantPITransferPaid : Bool
    repositoryCustodyTransferPaid : Bool
    sameSimulationStateTransferPaid : Bool
    qidCoordinate : String
    deweyTraversal : String

open ScientificResourceContinuityReceipt public

loureiroToLiResourceContinuity : ScientificResourceContinuityReceipt
loureiroToLiResourceContinuity = scientific-resource-continuity-receipt
  "First-principles modeling of ion acoustic turbulence in collisionless reconnection / Role of ion acoustic instability in magnetic reconnection — Dion Li; Zhuo Liu; Nuno F. Loureiro"
  "arXiv:2505.08983; DOI 10.1017/S002237782510113X"
  "https://meetings-archive.aps.org/dpp/2025/cm12/9/"
  "NSF GRFP; DOE DE-SC0022012; DOE DE-FG02-91-ER54109; NERSC FES-ERCAP0026577; NERSC facility contract DE-AC02-05CH11231"
  "Kinetic route to helicity-constrained decay — Dion Li"
  "arXiv:2602.17514; DOI 10.1103/j5p4-jj3d"
  "https://doi.org/10.1103/j5p4-jj3d"
  "DOE DE-FG02-91ER54109; NERSC FES-ERCAP0026577; NERSC facility contract DE-AC02-05CH11231; NSF GRFP 2141064"
  true true false true false false false
  "Q51287446"
  "530 Physics"

record ResourceContinuityBoundary : Set where
  constructor resource-continuity-boundary
  field
    repeatedAwardIdentifierImpliesGrantPITransfer : Bool
    repeatedNERSCAllocationImpliesSameSimulationBytes : Bool
    repeatedFacilityContractImpliesRepositoryTransfer : Bool
    absentDEsc0022012InSoloPaperProvesGrantEnded : Bool
    exactResourceReuseMayGuideGrantAndSimulationSearch : Bool

open ResourceContinuityBoundary public

canonicalResourceContinuityBoundary : ResourceContinuityBoundary
canonicalResourceContinuityBoundary = resource-continuity-boundary
  false false false false true

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
