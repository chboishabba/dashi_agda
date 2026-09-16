module DASHI.Culture.MissingDeceasedTwentyScientistRound86NingDODOIGFOIALogBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ROUND 86 / NING LI DOD OIG FOIA LOG BOUNDARY
--
-- The official DoD OIG FY2022 FOIA log records request
-- DODOIG-2022-001077, requester Carly Boye, submitted/received/closed
-- 2022-07-14, seeking declassified records regarding AC Gravity LLC or a
-- redacted person, particularly the AC Gravity grant.
--
-- The public log pays request existence and same-day closure only.  It does
-- not expose the closure disposition or a response package, so it cannot pay
-- a completed substantive search, no-records conclusion, classification,
-- concealment, success or failure.
------------------------------------------------------------------------

record DODOIGFOIALogReceipt : Set where
  constructor dodOIGFOIALogReceipt
  field
    requestReference : String
    requesterReference : String
    subjectReference : String
    submittedReference : String
    receivedReference : String
    closedReference : String
    publicDispositionReference : String
    completedAgencyRecordsSearchPaid : Bool

canonicalDODOIGFOIALogReceipt : DODOIGFOIALogReceipt
canonicalDODOIGFOIALogReceipt = dodOIGFOIALogReceipt
  "DODOIG-2022-001077"
  "Carly Boye"
  "declassified records regarding AC Gravity LLC or a redacted person, particularly the AC Gravity grant"
  "2022-07-14"
  "2022-07-14"
  "2022-07-14"
  "underidentified on the acquired public log surface"
  false

dodOIGRequestLogPaid : Bool
dodOIGRequestLogPaid = true

sameDayClosurePaid : Bool
sameDayClosurePaid = true

closureDispositionUnderidentified : Bool
closureDispositionUnderidentified = true

responsePackageLocated : Bool
responsePackageLocated = false

completedSubstantiveSearchPaid : Bool
completedSubstantiveSearchPaid = false

sameDayClosureDoesNotPayNoRecords : Bool
sameDayClosureDoesNotPayNoRecords = true

sameDayClosureDoesNotPayReferral : Bool
sameDayClosureDoesNotPayReferral = true

sameDayClosureDoesNotPayClassification : Bool
sameDayClosureDoesNotPayClassification = true

sameDayClosureDoesNotPayConcealment : Bool
sameDayClosureDoesNotPayConcealment = true

sameDayClosureDoesNotPayPrototypeSuccess : Bool
sameDayClosureDoesNotPayPrototypeSuccess = true

sameDayClosureDoesNotPayPrototypeFailure : Bool
sameDayClosureDoesNotPayPrototypeFailure = true

separateFromOSDJS23F0043 : Bool
separateFromOSDJS23F0043 = true

multipleFOIARoutesDoNotMultiplyNoRecordsEvidence : Bool
multipleFOIARoutesDoNotMultiplyNoRecordsEvidence = true

primaryArmyInstrumentStillUnacquired : Bool
primaryArmyInstrumentStillUnacquired = true

armyOutcomeStillUnresolved : Bool
armyOutcomeStillUnresolved = true

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record NingDODOIGFOIABoundary : Set where
  constructor ningDODOIGFOIABoundary
  field
    requestPaid : Bool
    requestPaidIsTrue : requestPaid ≡ true
    sameDayClosure : Bool
    sameDayClosureIsTrue : sameDayClosure ≡ true
    dispositionUnderidentified : Bool
    dispositionUnderidentifiedIsTrue : dispositionUnderidentified ≡ true
    noRecordsBlocked : Bool
    noRecordsBlockedIsTrue : noRecordsBlocked ≡ true

canonicalNingDODOIGFOIABoundary : NingDODOIGFOIABoundary
canonicalNingDODOIGFOIABoundary =
  ningDODOIGFOIABoundary true refl true refl true refl true refl
