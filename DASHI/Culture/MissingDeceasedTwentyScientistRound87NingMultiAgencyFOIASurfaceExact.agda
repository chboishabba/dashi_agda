module DASHI.Culture.MissingDeceasedTwentyScientistRound87NingMultiAgencyFOIASurfaceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ROUND 87 / NING LI MULTI-AGENCY FOIA SURFACE
--
-- Three source-bound public-request surfaces are now distinguished:
--   * FBI FY2021 FOIA log, case 1499382-000, opened 2021-06-24,
--     subject AC Gravity, LLC; disposition/response package unresolved.
--   * DoD OIG FY2022 FOIA log, DODOIG-2022-001077, received and closed
--     2022-07-14; exact closure disposition unresolved on the public log.
--   * OSD/JS 23-F-0043, administratively closed after a narrowing request
--     was not answered; no responsive records released through that path.
--
-- Request multiplicity is not evidence multiplicity for the proposition
-- "no records exist".  Each route retains its own procedural status.
------------------------------------------------------------------------

record FOIARouteReceipt : Set where
  constructor foiaRouteReceipt
  field
    agencyReference : String
    requestReference : String
    subjectReference : String
    proceduralStatusReference : String
    responsePackageLocated : Bool
    completedRecordsSearchPaid : Bool
    noRecordsConclusionPaid : Bool

fbiRoute : FOIARouteReceipt
fbiRoute = foiaRouteReceipt
  "Federal Bureau of Investigation"
  "1499382-000"
  "AC Gravity, LLC"
  "opened 2021-06-24; disposition unresolved on acquired log surface"
  false
  false
  false

dodOIGRoute : FOIARouteReceipt
dodOIGRoute = foiaRouteReceipt
  "Department of Defense Office of Inspector General"
  "DODOIG-2022-001077"
  "declassified AC Gravity / grant records"
  "received and closed 2022-07-14; exact disposition unresolved"
  false
  false
  false

osdJSRoute : FOIARouteReceipt
osdJSRoute = foiaRouteReceipt
  "Office of the Secretary of Defense / Joint Staff"
  "23-F-0043"
  "records concerning the 2001 AC Gravity / Ning Li DoD award"
  "administratively closed after requester did not narrow a request described as not reasonably described"
  true
  false
  false

fbiACGravityRequestLogPaid : Bool
fbiACGravityRequestLogPaid = true

dodOIGACGravityRequestLogPaid : Bool
dodOIGACGravityRequestLogPaid = true

osdJSProceduralClosurePaid : Bool
osdJSProceduralClosurePaid = true

fbiDispositionPaid : Bool
fbiDispositionPaid = false

dodOIGExactDispositionPaid : Bool
dodOIGExactDispositionPaid = false

requestCountDoesNotEqualIndependentNoRecordsCount : Bool
requestCountDoesNotEqualIndependentNoRecordsCount = true

threeRoutesDoNotPayThreeCompletedSearches : Bool
threeRoutesDoNotPayThreeCompletedSearches = true

threeRoutesDoNotPayNoRecordsExist : Bool
threeRoutesDoNotPayNoRecordsExist = true

threeRoutesDoNotPayClassification : Bool
threeRoutesDoNotPayClassification = true

threeRoutesDoNotPayConcealment : Bool
threeRoutesDoNotPayConcealment = true

proceduralHeterogeneityMustBeRetained : Bool
proceduralHeterogeneityMustBeRetained = true

primaryArmyInstrumentStillUnacquired : Bool
primaryArmyInstrumentStillUnacquired = true

armyOutcomeStillUnresolved : Bool
armyOutcomeStillUnresolved = true

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record NingMultiAgencyFOIABoundary : Set where
  constructor ningMultiAgencyFOIABoundary
  field
    fbiRoutePaid : Bool
    fbiRoutePaidIsTrue : fbiRoutePaid ≡ true
    dodOIGRoutePaid : Bool
    dodOIGRoutePaidIsTrue : dodOIGRoutePaid ≡ true
    osdJSRoutePaid : Bool
    osdJSRoutePaidIsTrue : osdJSRoutePaid ≡ true
    noRecordsAggregationBlocked : Bool
    noRecordsAggregationBlockedIsTrue : noRecordsAggregationBlocked ≡ true

canonicalNingMultiAgencyFOIABoundary : NingMultiAgencyFOIABoundary
canonicalNingMultiAgencyFOIABoundary =
  ningMultiAgencyFOIABoundary true refl true refl true refl true refl
