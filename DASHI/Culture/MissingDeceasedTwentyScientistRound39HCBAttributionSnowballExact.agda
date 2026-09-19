module DASHI.Culture.MissingDeceasedTwentyScientistRound39HCBAttributionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Culture.MissingDeceasedTwentyScientistRound32MonicaHCBRolePaymentExact as R32
import DASHI.Culture.MissingDeceasedTwentyScientistRound34McCaslandHCBPublicReferenceExact as R34
import DASHI.Culture.MissingDeceasedTwentyScientistRound36HCBContractDerivativeIdentityExact as R36
import DASHI.Culture.MissingDeceasedTwentyScientistRound38ContractTemporalNonFactorabilityExact as R38

------------------------------------------------------------------------
-- ROUND 39: HCB ATTRIBUTION SNOWBALL
--
-- The HCB investigation now contains several genuinely useful source roles at
-- different granularities.  Search may snowball across them, but attribution
-- and claim semantics must not collapse.  A project-role source, a programme-
-- reference source, an exact-contract derivative source, and a later-persistence
-- source each pay only their own bounded proposition.
--
-- This is a domain instantiation of the repository-wide attribution invariant:
-- citations preserve source identity/role but import neither proof nor authority.
------------------------------------------------------------------------

data HCBSourceRole : Set where
  exactProjectRoleSource : HCBSourceRole
  programmeReferenceSource : HCBSourceRole
  contractDerivativeIdentitySource : HCBSourceRole
  laterContractPersistenceSource : HCBSourceRole

record HCBSourceRoleBoundary : Set where
  constructor hcb-source-role-boundary
  field
    role : HCBSourceRole
    sourceLabel : String
    paidClaim : String
    unpaidClaim : String
    sourceIdentityRetained : Bool
    sourceKindRetained : Bool
    claimGranularityRetained : Bool
    citationImportsProof : Bool
    citationCreatesAuthority : Bool

open HCBSourceRoleBoundary public

monicaProjectRoleBoundary : HCBSourceRoleBoundary
monicaProjectRoleBoundary = hcb-source-role-boundary
  exactProjectRoleSource
  "Round 32 Engineers Council Mondaloy/HBTD project-award surface"
  "Monica Jacinto has a source-backed relation to the exact Mondaloy/HBTD project object"
  "Neil McCasland shares that exact task or contract role"
  true true true false false

mccaslandProgrammeReferenceBoundary : HCBSourceRoleBoundary
mccaslandProgrammeReferenceBoundary = hcb-source-role-boundary
  programmeReferenceSource
  "Round 34 AIAA panel participation + contemporaneous conference reporting"
  "Neil McCasland personally referenced AFRL Hydrocarbon Boost contemporaneously"
  "Neil McCasland held a role on FA9300-07-C-0001 or the Mondaloy materials task"
  true true true false false

contractDerivativeBoundary : HCBSourceRoleBoundary
contractDerivativeBoundary = hcb-source-role-boundary
  contractDerivativeIdentitySource
  "Round 36 exact-contract patent derivative surface"
  "named technical inventors occur on derivatives explicitly tied to FA9300-07-C-0001"
  "the derivative inventor list is an exhaustive contract roster or proves retained-person non-participation"
  true true true false false

laterPersistenceBoundary : HCBSourceRoleBoundary
laterPersistenceBoundary = hcb-source-role-boundary
  laterContractPersistenceSource
  "Round 38 later modification/derivative lineage"
  "FA9300-07-C-0001 persists into later contract and technical lineage"
  "a particular person held an exact 2011-2013 role"
  true true true false false

round39Boundaries : List HCBSourceRoleBoundary
round39Boundaries =
  monicaProjectRoleBoundary ∷
  mccaslandProgrammeReferenceBoundary ∷
  contractDerivativeBoundary ∷
  laterPersistenceBoundary ∷
  []

round39BoundaryCount : Nat
round39BoundaryCount = 4

record HCBAttributionJoinBoundary : Set where
  constructor hcb-attribution-join-boundary
  field
    searchMaySnowballAcrossSourceRoles : Bool
    sourceRoleJoinTransfersHistoricalClaim : Bool
    sourceRoleJoinCreatesProof : Bool
    sourceRoleJoinCreatesAuthority : Bool
    exactRoleStillRequiresExactRoleReceipt : Bool
    sourceSpecificUnpaidClaimsRemainUnpaid : Bool

open HCBAttributionJoinBoundary public

canonicalHCBAttributionJoinBoundary : HCBAttributionJoinBoundary
canonicalHCBAttributionJoinBoundary = hcb-attribution-join-boundary
  true
  false
  false
  false
  true
  true

sourceRoleJoinTransfersHistoricalClaim : Bool
sourceRoleJoinTransfersHistoricalClaim = false

sourceRoleJoinCreatesProof : Bool
sourceRoleJoinCreatesProof = false

sourceRoleJoinCreatesAuthority : Bool
sourceRoleJoinCreatesAuthority = false

projectRoleDoesNotBecomeProgrammeRole : Bool
projectRoleDoesNotBecomeProgrammeRole = true

programmeReferenceDoesNotBecomeTaskRole : Bool
programmeReferenceDoesNotBecomeTaskRole = true

derivativeIdentityDoesNotBecomeExhaustiveRoster : Bool
derivativeIdentityDoesNotBecomeExhaustiveRoster = true

laterPersistenceDoesNotBecomeEarlierPersonalRole : Bool
laterPersistenceDoesNotBecomeEarlierPersonalRole = true

round39UsesCanonicalAttributionSnowball : Bool
round39UsesCanonicalAttributionSnowball = true

round39MonicaReceiptRetained : Bool
round39MonicaReceiptRetained = true

round39McCaslandReceiptRetained : Bool
round39McCaslandReceiptRetained = true

round39DerivativeReceiptsRetained : Bool
round39DerivativeReceiptsRetained = true

round39TemporalGuardRetained : Bool
round39TemporalGuardRetained = true

round39H2PaidCount : Nat
round39H2PaidCount = 0

round39H3PaidCount : Nat
round39H3PaidCount = 0

round39Pareto : String
round39Pareto = "Continue snowball acquisition across HCB sources, but never transfer a claim across source roles merely because the sources concern the same programme or contract. A future H2 promotion still requires a literal contemporaneous identity-bearing exact-role receipt; citations and cross-source joins create neither proof nor authority."
