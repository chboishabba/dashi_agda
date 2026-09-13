module DASHI.Culture.NingLiGovernmentRequestLogSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as A

------------------------------------------------------------------------
-- GOVERNMENT REQUEST-LOG SNOWBALL FOR NING LI / AC GRAVITY
--
-- Request logs prove that a request/search case existed and sometimes preserve
-- a disposition label.  They do not disclose the response package unless that
-- package is independently acquired.  This owner therefore treats the case IDs
-- as high-value acquisition coordinates only.
------------------------------------------------------------------------

record GovernmentRequestLogEntry : Set where
  constructor government-request-log-entry
  field
    agency : String
    caseNumber : String
    openedOrLogYear : String
    subjectOrRequest : String
    dispositionOrClosure : String
    sourceReference : String
    responsePackageLocated : Bool
    responseContentsPaid : Bool
    noRecordsFindingPaid : Bool
    classificationFindingPaid : Bool
    nextAcquisition : String

open GovernmentRequestLogEntry public

dtic2019Source : A.AttributedSource
dtic2019Source = A.mkNoDOISource
  "Defense Technical Information Center FOIA log"
  "DTIC FOIA Log 2010-2020"
  "public record copy hosted by GovernmentAttic"
  "2019 log"
  "https://www.governmentattic.org/38docs/DTICfoiaLog_2010-2020.pdf"
  A.archivalSource
  "captured FOIA-log manifestation showing 2019 case 4, requester Klotz, request 'Search on Ning Li or AC Gravity, LLC', disposition 'Sent to requester 10-12-18'; pays only the existence/disposition text of the logged request, not the contents of what was sent"
  A.publicAttribution

fbi2021Source : A.AttributedSource
fbi2021Source = A.mkNoDOISource
  "Federal Bureau of Investigation"
  "FOIA Log 2021 Part 01"
  "FBI Vault"
  "2021"
  "https://vault.fbi.gov/foia-log-2021-part-01/FOIA%20Log%202021%20Part%2001%20%28Final%29/"
  A.governmentSource
  "primary FBI FOIA-log manifestation listing case 1499382 revision 000, opened 2021-06-24, subject AC Gravity, LLC; does not expose the request text, disposition, response package or responsive records in the cited log surface"
  A.publicAttribution

dodOIG2022Source : A.AttributedSource
dodOIG2022Source = A.mkNoDOISource
  "U.S. Department of Defense Office of Inspector General"
  "Freedom of Information Act Case Log Fiscal Year 2022 (Redacted)"
  "DoD OIG public FOIA case log"
  "2022"
  "https://media.defense.gov/2025/Mar/20/2003673003/-1/-1/1/FOIA%20CASE%20LOG%20FISCAL%20YEAR%202022%20%28REDACTED%29.PDF"
  A.governmentSource
  "primary DoD OIG log listing DODOIG-2022-001077, requester Carly Boye, request/received/closed 2022-07-14, summary seeking declassified records regarding AC Gravity LLC and particularly the AC Gravity grant; the log alone does not state what disposition or response package was supplied"
  A.publicAttribution

dtic2019NingLiACGravityRequest : GovernmentRequestLogEntry
dtic2019NingLiACGravityRequest = government-request-log-entry
  "Defense Technical Information Center"
  "2019-4"
  "2019 log; disposition dated 2018-10-12 in the published table"
  "Search on Ning Li or AC Gravity, LLC"
  "Sent to requester 10-12-18"
  "DTIC FOIA Log 2010-2020"
  false false false false
  "recover the actual response/bibliography/document package sent to requester Klotz and identify every DTIC accession/document returned by the search"

fbiCaseNumber : String
fbiCaseNumber = "1499382-000"

fbi2021ACGravityRequest : GovernmentRequestLogEntry
fbi2021ACGravityRequest = government-request-log-entry
  "Federal Bureau of Investigation"
  fbiCaseNumber
  "opened 2021-06-24"
  "AC Gravity, LLC"
  "not exposed in the cited FBI log row"
  "FBI Vault FOIA Log 2021 Part 01"
  false false false false
  "recover the request and FBI response/disposition package for 1499382-000 before inferring FBI records, investigation, no-records state or classification"

dodOIGCaseNumber : String
dodOIGCaseNumber = "DODOIG-2022-001077"

dodOIG2022ACGravityRequest : GovernmentRequestLogEntry
dodOIG2022ACGravityRequest = government-request-log-entry
  "Department of Defense Office of Inspector General"
  dodOIGCaseNumber
  "request/received/closed 2022-07-14"
  "Declassified records regarding AC Gravity LLC, particularly regarding the AC Gravity grant"
  "same-day closure shown by log; outcome text not exposed in the cited row"
  "DoD OIG FY2022 FOIA Case Log"
  false false false false
  "recover the actual response/closure letter for DODOIG-2022-001077 and distinguish referral, duplication, no-records, exemption or other procedural disposition"

requestLogSnowball : List GovernmentRequestLogEntry
requestLogSnowball =
  dtic2019NingLiACGravityRequest ∷
  fbi2021ACGravityRequest ∷
  dodOIG2022ACGravityRequest ∷ []

requestLogPaysResponseContents : Bool
requestLogPaysResponseContents = false

record RequestLogBoundary : Set where
  constructor request-log-boundary
  field
    loggedRequestProvesResponsiveRecordsExist : Bool
    loggedRequestProvesNoRecords : Bool
    loggedRequestProvesInvestigation : Bool
    dispositionLabelPaysUnseenPackageContents : Bool
    caseIdentifierMayNominateResponsePackageAcquisition : Bool

canonicalRequestLogBoundary : RequestLogBoundary
canonicalRequestLogBoundary = request-log-boundary false false false false true
