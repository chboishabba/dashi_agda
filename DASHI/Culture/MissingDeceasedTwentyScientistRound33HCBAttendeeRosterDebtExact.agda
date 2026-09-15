module DASHI.Culture.MissingDeceasedTwentyScientistRound33HCBAttendeeRosterDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- ROUND 33: HCB INDUSTRY-DAY IDENTITY-BEARING ACQUISITION DEBT
--
-- The 18 September 2012 HCB industry day is unusually valuable because the
-- public notice says attendee Full Name and Organization were to be collected,
-- while attendance was restricted to eligible DoD, NASA and U.S. contractor
-- personnel for discussion that included ITAR / Distribution-C information.
--
-- The public notice itself names no attendee roster and has no attachments.
-- Therefore it identifies a high-alpha documentary target without paying any
-- particular person's attendance.  Restricted technical content also says
-- nothing by itself about later targeting, suppression, event causation, or H3.
------------------------------------------------------------------------

record IdentityBearingAcquisitionDebt : Set where
  constructor identity-bearing-acquisition-debt
  field
    source : Attribution.AttributedSource
    eventIdentifier : String
    eventDate : String
    eventLocation : String
    programmeObject : String
    industryDayIdentityPaid : Bool
    attendeeNamesWereCollectedPaid : Bool
    attendeeOrganisationWasCollectedPaid : Bool
    restrictedTechnicalBriefingPaid : Bool
    publicAttendeeRosterPaid : Bool
    publicBriefingDistributionListPaid : Bool
    mccaslandAttendancePaid : Bool
    monicaAttendancePaid : Bool
    crossPersonSameEventPaid : Bool
    crossPersonSameObjectRolePaid : Bool
    pays : String
    doesNotPay : String
    nextLiteralAcquisition : String

open IdentityBearingAcquisitionDebt public

hcbIndustryDaySource : Attribution.AttributedSource
hcbIndustryDaySource = Attribution.mkNoDOISource
  "U.S. Air Force / SAM.gov"
  "Industry Day Briefing on the current status of the Hydrocarbon Boost Engine Technology program"
  "SAM.gov special notice, FA9300-07-C-0001"
  "2012"
  "https://sam.gov/opp/d9e3f446b7ed4e0db199b3dd75e405c0/view"
  Attribution.governmentSource
  "primary notice for the 18 September 2012 HCB industry day; records event scope, eligibility restrictions, organiser contacts and the requirement for attendee identity/organisation data"
  Attribution.publicAttribution

hcbIndustryDaySnowball : Snowball.SourceRoleSnowballReceipt hcbIndustryDaySource
hcbIndustryDaySnowball = Snowball.canonicalSourceRoleSnowballReceipt hcbIndustryDaySource

hcbRosterDebt : IdentityBearingAcquisitionDebt
hcbRosterDebt = identity-bearing-acquisition-debt
  hcbIndustryDaySource
  "FA9300-07-C-0001 HCB industry-day briefing"
  "18 September 2012"
  "Los Angeles AFB, Gordon Conference Center, El Segundo, California"
  "Hydrocarbon Boost Engine Technology / oxygen-rich staged combustion demonstration"
  true
  true
  true
  true
  false
  false
  false
  false
  false
  false
  "exact event identity; HCB programme object; contemporaneous date/location; organiser contacts; attendee-name and attendee-organisation collection requirement; restricted technical briefing boundary"
  "that McCasland attended, that Monica Jacinto attended, that they shared an event or work package, H2, H3, classification of any later event, suppression, targeting, or causal linkage"
  "acquire the attendee registration/attendance roster, briefing distribution list, visitor-access record, organiser correspondence, after-action record or briefing approval chain for the 18 September 2012 HCB industry day; test literal names/organisations before any promotion"

industryDayIdentityPaid : Bool
industryDayIdentityPaid = true

attendeeNamesWereCollectedPaid : Bool
attendeeNamesWereCollectedPaid = true

attendeeOrganisationWasCollectedPaid : Bool
attendeeOrganisationWasCollectedPaid = true

restrictedTechnicalBriefingPaid : Bool
restrictedTechnicalBriefingPaid = true

publicAttendeeRosterPaid : Bool
publicAttendeeRosterPaid = false

publicBriefingDistributionListPaid : Bool
publicBriefingDistributionListPaid = false

mccaslandAttendancePaid : Bool
mccaslandAttendancePaid = false

monicaAttendancePaid : Bool
monicaAttendancePaid = false

crossPersonSameEventPaid : Bool
crossPersonSameEventPaid = false

restrictedMeetingCannotPayLaterTargeting : Bool
restrictedMeetingCannotPayLaterTargeting = true

identityCollectionRequirementCannotPaySpecificAttendance : Bool
identityCollectionRequirementCannotPaySpecificAttendance = true

absenceOfPublicRosterCannotPayNonattendance : Bool
absenceOfPublicRosterCannotPayNonattendance = true

round33H2PaidCount : Nat
round33H2PaidCount = 0

round33H3PaidCount : Nat
round33H3PaidCount = 0

round33Pareto : String
round33Pareto = "The HCB programme search now exposes an identity-bearing missing source rather than a vague archival gap: the 18-Sep-2012 FA9300-07-C-0001 industry-day registration/attendance and distribution records. The public notice states that names and organisations were collected but publishes no roster. Acquire roster, visitor-access, organiser correspondence, distribution list or after-action records; only literal name evidence can pay McCasland or Monica attendance. Restricted technical content does not pay H3."