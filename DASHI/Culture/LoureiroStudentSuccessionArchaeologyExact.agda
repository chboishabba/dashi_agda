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

------------------------------------------------------------------------
-- Award-scope archaeology / control.
--
-- DOE's own active-award tables identify DE-FG02-91ER54109 as an MIT award,
-- title "Theoretical Research in Advanced Physics and Technology", historically
-- listing Peter Catto as PI. MIT audit schedules retain the same institutional
-- award title. APS and 2026 EPS records show the identifier supporting multiple
-- MIT/PSFC plasma projects across years, including work unrelated to Loureiro/Li.
-- Therefore exact identifier reuse across Loureiro's death pays institutional
-- resource continuity, not a personal Loureiro-to-Li grant transfer.
------------------------------------------------------------------------

record AwardScopeArchaeology : Set where
  constructor award-scope-archaeology
  field
    awardIdentifier : String
    primaryGovernmentSource : String
    primaryGovernmentLink : String
    historicalAwardee : String
    historicalPI : String
    institutionalAwardTitle : String
    primaryInstitutionalSource : String
    primaryInstitutionalLink : String
    independent2026UseSource : String
    independent2026UseLink : String
    institutionalScopePaid : Bool
    loureiroPersonalGrantIdentityPaid : Bool
    postLossReusePaysInstitutionalResourceContinuity : Bool
    postLossReusePaysPITransfer : Bool
    deweyTraversal : String

open AwardScopeArchaeology public

mitDEFG0291ER54109Scope : AwardScopeArchaeology
mitDEFG0291ER54109Scope = award-scope-archaeology
  "DE-FG02-91ER54109"
  "U.S. Department of Energy Office of Science active-award table for Massachusetts, FY2010/FY2011"
  "https://science.osti.gov/-/media/_/pdf/universities/SC_StatebyState_awards_FY2010.pdf"
  "Massachusetts Institute of Technology"
  "Peter Catto"
  "Theoretical Research in Advanced Physics and Technology"
  "MIT Uniform Guidance / Schedule of Expenditures of Federal Awards"
  "https://vpf.mit.edu/sites/default/files/downloads/AuditReport/2024-MIT-Uniform-Guidance-Report.pdf"
  "EPS Plasma Physics Conference 2026: Jeffrey Freidberg / Earl Marmar MHD energy-conversion work"
  "https://indico.ukaea.uk/event/449/contributions/1946/"
  true false true false
  "530 Physics"

record ResourceContinuityBoundary : Set where
  constructor resource-continuity-boundary
  field
    repeatedAwardIdentifierImpliesGrantPITransfer : Bool
    repeatedNERSCAllocationImpliesSameSimulationBytes : Bool
    repeatedFacilityContractImpliesRepositoryTransfer : Bool
    absentDEsc0022012InSoloPaperProvesGrantEnded : Bool
    institutionalAwardReuseEqualsPersonalGrantTransfer : Bool
    historicalDifferentPIBlocksLoureiroPersonalGrantReading : Bool
    unrelated2026UseSupportsInstitutionalScopeReading : Bool
    exactResourceReuseMayGuideGrantAndSimulationSearch : Bool

open ResourceContinuityBoundary public

canonicalResourceContinuityBoundary : ResourceContinuityBoundary
canonicalResourceContinuityBoundary = resource-continuity-boundary
  false false false false false true true true

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
