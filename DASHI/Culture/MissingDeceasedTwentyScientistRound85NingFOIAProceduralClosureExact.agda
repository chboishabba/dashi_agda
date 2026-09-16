module DASHI.Culture.MissingDeceasedTwentyScientistRound85NingFOIAProceduralClosureExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ROUND 85 / NING LI FOIA PROCEDURAL CLOSURE
--
-- MuckRock docket 23-F-0043 records an OSD/JS FOIA request seeking records
-- about the 2001 AC Gravity award.  The office asked the requester to narrow
-- a request it considered not reasonably described and later administratively
-- closed it when no narrowing response was received.  No responsive records
-- were released through this path.
--
-- That procedural history is not a completed substantive records search and
-- cannot pay absence, concealment, classification, success or failure.
------------------------------------------------------------------------

record FOIAClosureReceipt : Set where
  constructor foiaClosureReceipt
  field
    requestReference : String
    requestedSubject : String
    closureReference : String
    closureReason : String
    recordsReleased : Bool
    completedAgencyRecordsSearchPaid : Bool

canonicalFOIAClosureReceipt : FOIAClosureReceipt
canonicalFOIAClosureReceipt = foiaClosureReceipt
  "OSD/JS FOIA 23-F-0043"
  "records concerning the 2001 AC Gravity / Ning Li DoD award"
  "MuckRock docket and OSD/JS final-response correspondence"
  "administratively closed after requester did not narrow a request described as not reasonably described"
  false
  false

foiaAdministrativeClosurePaid : Bool
foiaAdministrativeClosurePaid = true

foiaNoResponsiveRecordsReleasedPaid : Bool
foiaNoResponsiveRecordsReleasedPaid = true

foiaCompletedAgencyRecordsSearchPaid : Bool
foiaCompletedAgencyRecordsSearchPaid = false

foiaClosureDoesNotPayCompletedRecordsSearch : Bool
foiaClosureDoesNotPayCompletedRecordsSearch = true

foiaClosureDoesNotPayNoRecordsExist : Bool
foiaClosureDoesNotPayNoRecordsExist = true

foiaClosureDoesNotPayConcealment : Bool
foiaClosureDoesNotPayConcealment = true

foiaClosureDoesNotPayClassification : Bool
foiaClosureDoesNotPayClassification = true

foiaClosureDoesNotPayPrototypeSuccess : Bool
foiaClosureDoesNotPayPrototypeSuccess = true

foiaClosureDoesNotPayPrototypeFailure : Bool
foiaClosureDoesNotPayPrototypeFailure = true

proceduralClosureDoesNotEraseOfficialAMCOMRoute : Bool
proceduralClosureDoesNotEraseOfficialAMCOMRoute = true

primaryArmyInstrumentStillUnacquired : Bool
primaryArmyInstrumentStillUnacquired = true

armyOutcomeStillUnresolved : Bool
armyOutcomeStillUnresolved = true

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record NingFOIAProceduralBoundary : Set where
  constructor ningFOIAProceduralBoundary
  field
    closurePaid : Bool
    closurePaidIsTrue : closurePaid ≡ true
    searchCompletionUnpaid : Bool
    searchCompletionUnpaidIsFalse : searchCompletionUnpaid ≡ false
    noRecordsConclusionBlocked : Bool
    noRecordsConclusionBlockedIsTrue : noRecordsConclusionBlocked ≡ true
    concealmentConclusionBlocked : Bool
    concealmentConclusionBlockedIsTrue : concealmentConclusionBlocked ≡ true

canonicalNingFOIAProceduralBoundary : NingFOIAProceduralBoundary
canonicalNingFOIAProceduralBoundary =
  ningFOIAProceduralBoundary true refl false refl true refl true refl
