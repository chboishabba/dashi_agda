module DASHI.Core.EventTimeOperationalPossessionEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EVENT-TIME OPERATIONAL POSSESSION EVIDENCE
--
-- Historical expertise, publication affiliation, current employment, active
-- project participation, repository/data access, and actual application-carrier
-- possession are distinct evidence coordinates.
------------------------------------------------------------------------

data ContinuityEvidenceKind : Set where
  historicalRole
  memorialRoleSummary
  publicationAffiliation
  currentEmploymentOrAppointment
  activeProjectRoster
  facilityOrRepositoryAccess
  calibrationOrConfigurationCustody
  sameCarrierOperationalUse
  : ContinuityEvidenceKind

record EventTimePossessionReceipt : Set where
  constructor event-time-possession-receipt
  field
    subject : String
    carrier : String
    eventDate : String
    evidenceKinds : List ContinuityEvidenceKind
    sourceReference : String
    boundedReading : String

open EventTimePossessionReceipt public

record EventTimeEvidenceBoundary : Set where
  constructor event-time-evidence-boundary
  field
    historicalRoleImpliesCurrentEmployment : Bool
    historicalRoleImpliesCurrentEmploymentIsFalse : historicalRoleImpliesCurrentEmployment ≡ false
    memorialSummaryImpliesEventTimeAccess : Bool
    memorialSummaryImpliesEventTimeAccessIsFalse : memorialSummaryImpliesEventTimeAccess ≡ false
    publicationAffiliationImpliesOperationalAccess : Bool
    publicationAffiliationImpliesOperationalAccessIsFalse : publicationAffiliationImpliesOperationalAccess ≡ false
    currentAppointmentImpliesSameCarrierPossession : Bool
    currentAppointmentImpliesSameCarrierPossessionIsFalse : currentAppointmentImpliesSameCarrierPossession ≡ false
    activeProjectRosterImpliesCalibrationCustody : Bool
    activeProjectRosterImpliesCalibrationCustodyIsFalse : activeProjectRosterImpliesCalibrationCustody ≡ false
    sameCarrierOperationalUseCanSupportEventTimePossession : Bool
    sameCarrierOperationalUseCanSupportEventTimePossessionIsTrue : sameCarrierOperationalUseCanSupportEventTimePossession ≡ true

canonicalEventTimeEvidenceBoundary : EventTimeEvidenceBoundary
canonicalEventTimeEvidenceBoundary = event-time-evidence-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl

data EventTimeReverseTarget : Set where
  acquireCurrentEmploymentOrAppointment
  acquireActiveProjectRoster
  acquireFacilityAccess
  acquireRepositoryOrDataAccess
  acquireCalibrationOrConfigurationCustody
  acquireSameCarrierOperationalUse
  : EventTimeReverseTarget
