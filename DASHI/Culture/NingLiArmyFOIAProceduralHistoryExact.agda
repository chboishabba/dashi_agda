module DASHI.Culture.NingLiArmyFOIAProceduralHistoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as A

------------------------------------------------------------------------
-- FOIA PROCEDURAL HISTORY FOR THE REPORTED AC GRAVITY / ARMY AGREEMENT
--
-- The 2022 request trail is useful only as a procedural source.  MuckRock
-- preserves DoD correspondence showing that case 23-F-0043 was administratively
-- closed because the requester did not respond to a five-day letter, and that
-- DoD invited reformulation under a new tracking number.  This is not a
-- substantive no-records finding and cannot support a suppression inference.
------------------------------------------------------------------------

muckRockFOIASource : A.AttributedSource
muckRockFOIASource = A.mkNoDOISource
  "Austin Thompson / U.S. Department of Defense FOIA correspondence"
  "Department of Defense Grant for AC Gravity LLC (2001)"
  "MuckRock request archive; DoD tracking 23-F-0043"
  "2022-2023"
  "https://www.muckrock.com/foi/united-states-of-america-10/department-of-defense-grant-for-ac-gravity-llc-2001-department-of-defense-defense-security-cooperation-agency-135084/"
  A.archivalSource
  "public archive of a FOIA request and agency correspondence; supports the procedural fact that case 23-F-0043 was administratively closed for non-response to a five-day letter and that reformulation was invited; does not establish that responsive records do or do not exist"
  A.publicAttribution

record FOIAProceduralHistory : Set where
  constructor foia-procedural-history
  field
    foiaTrackingNumber : String
    originalRequestDate : String
    administrativeClosureDate : String
    closureReason : String
    agencyLaterClarificationDate : String
    reformulationInvitation : String
    administrativelyClosedForNoResponse : Bool
    substantiveSearchCompletedPaid : Bool
    noResponsiveRecordsFindingPaid : Bool
    classificationExemptionFindingPaid : Bool
    reformulationWasExplicitlyInvited : Bool

open FOIAProceduralHistory public

canonicalFOIAHistory : FOIAProceduralHistory
canonicalFOIAHistory = foia-procedural-history
  "23-F-0043"
  "2022-10-12"
  "2022-11-04"
  "administratively closed because the office had not received a response to its five-day letter"
  "2023-10-30"
  "agency stated the requester could reformulate the request and have a new case opened under a new tracking number"
  true
  false
  false
  false
  true

foiaTrackingNumber : String
foiaTrackingNumber = "23-F-0043"

administrativelyClosedForNoResponse : Bool
administrativelyClosedForNoResponse = true

foiaClosurePaysNoRecordsFinding : Bool
foiaClosurePaysNoRecordsFinding = false

foiaClosurePaysClassificationFinding : Bool
foiaClosurePaysClassificationFinding = false

reformulationWasExplicitlyInvited : Bool
reformulationWasExplicitlyInvited = true

record FOIABoundary : Set where
  constructor foia-boundary
  field
    proceduralClosureEqualsSubstantiveNoRecordsFinding : Bool
    proceduralClosureProvesSuppression : Bool
    repeatedFollowUpsCreateSearchResult : Bool
    newWellScopedRequestMayStillResolveResidual : Bool

canonicalFOIABoundary : FOIABoundary
canonicalFOIABoundary = foia-boundary false false false true

nextFOIAAcquisition : String
nextFOIAAcquisition =
  "submit or locate a properly scoped request to Army AMCOM/AMC/records custodians keyed to DAAH01-01-9-R001, the awarding office AMSAM-AC-RD-BA, awardee name variants AC Gravity LLC/LLD, effective/completion dates, and requested categories: agreement, SOW, payment/accounting, technical deliverables, closeout and disposition"
