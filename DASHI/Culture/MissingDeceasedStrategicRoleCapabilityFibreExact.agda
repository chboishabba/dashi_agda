module DASHI.Culture.MissingDeceasedStrategicRoleCapabilityFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROLE != CAPABILITY
--
-- Scientist/non-scientist is too coarse for the cohort.  A manager may know
-- programme topology; an administrator may route personnel/budgets; a property
-- custodian may see inventory movement; a technician may know apparatus state.
-- Capability is therefore a time-indexed fibre independent of occupational label.
------------------------------------------------------------------------

data RoleClass : Set where
  scientist engineer manager administrator custodian technician otherRole : RoleClass

record RoleCapabilityFibre : Set where
  constructor role-capability-fibre
  field
    personReference : String
    role : RoleClass
    observationTime : String
    technicalKnowledge : Nat
    physicalAccess : Nat
    informationRouting : Nat
    inventoryVisibility : Nat
    programmeCoordination : Nat
    clearanceScope : Nat
    sourceReference : String
    sourceClass : String
    exactRoleIdentityPaid : Bool
    exactCapabilityScopePaid : Bool

open RoleCapabilityFibre public

managerFixture : RoleCapabilityFibre
managerFixture = role-capability-fibre
  "abstract programme manager control"
  manager
  "fixture"
  2 2 5 3 5 4
  "finite witness only"
  "formal fixture"
  true true

scientistFixture : RoleCapabilityFibre
scientistFixture = role-capability-fibre
  "abstract specialist scientist control"
  scientist
  "fixture"
  5 2 1 1 2 3
  "finite witness only"
  "formal fixture"
  true true

managerMayExceedScientistOnProgrammeCoordination : Bool
managerMayExceedScientistOnProgrammeCoordination = true

roleLabelDoesNotDetermineCapability : Bool
roleLabelDoesNotDetermineCapability = true

------------------------------------------------------------------------
-- Cohort-specific acquisition routing.  These are search obligations, not
-- promotion of the speculative narratives associated with each person.
------------------------------------------------------------------------

record RoleCapabilityAcquisition : Set where
  constructor role-capability-acquisition
  field
    person : String
    reportedRole : String
    candidateOperationalCapability : String
    alreadyPaid : String
    unpaidPrimaryObject : String
    speculativeNarrativeDoesNotPayCapability : Bool

open RoleCapabilityAcquisition public

chavezRoleCapabilityTarget : RoleCapabilityAcquisition
chavezRoleCapabilityTarget = role-capability-acquisition
  "Anthony Chavez (missing Los Alamos identity)"
  "reported retired HVAC technician / construction foreman; identity weld to LANL engineering profile remains unpaid"
  "facility access, maintenance history, construction routing, apparatus adjacency"
  "missing-person identity and separate LANL Anthony-Chavez engineering candidate retained without merge"
  "primary LANL employment/role history plus same-person receipt and any dated facility/access scope"
  true

casiasRoleCapabilityTarget : RoleCapabilityAcquisition
casiasRoleCapabilityTarget = role-capability-acquisition
  "Melissa Casias"
  "reported LANL administrative role"
  "information routing, personnel/badge workflow, administrative programme visibility"
  "role retained as non-scientific in scientific-work coverage; forensic state remains separate"
  "primary LANL employment/duty description and dated badge/routing scope; primary forensic/electronic-device records where releasable"
  true

garciaRoleCapabilityTarget : RoleCapabilityAcquisition
stevenGarciaRoleCapabilityTarget : RoleCapabilityAcquisition
stevenGarciaRoleCapabilityTarget = role-capability-acquisition
  "Steven Abel Garcia"
  "reported property custodian associated with KCNSC Albuquerque"
  "inventory visibility, property-accountability workflow, asset transfer visibility"
  "New Mexico missing-person identity/date; employer/property scope not yet primary-paid"
  "primary employer/contract duty description, property-accountability system scope and event-time assignment"
  true

record RoleCapabilityBoundary : Set where
  constructor role-capability-boundary
  field
    scientistRoleImpliesHighestOperationalKnowledge : Bool
    nonScientistRoleImpliesNoSensitiveKnowledge : Bool
    administrativeRoleImpliesClearance : Bool
    custodianRoleImpliesSpecificInventoryAnomaly : Bool
    occupationalLabelMaySeedCapabilityAcquisition : Bool
    capabilityMustBeDated : Bool

canonicalRoleCapabilityBoundary : RoleCapabilityBoundary
canonicalRoleCapabilityBoundary = role-capability-boundary
  false false false false true true
