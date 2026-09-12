module DASHI.Culture.MissingDeceasedReportedAnomalyAttributionLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedInvestigativeAttributedSourceAtlasExact as Sources

------------------------------------------------------------------------
-- REPORTED-ANOMALY ATTRIBUTION LEDGER
--
-- This ledger exists so high-salience journalism/community claims can nominate
-- primary acquisitions without becoming primary facts.  Every anomaly carries
-- its source class, current payment state, and exact next receipt.
------------------------------------------------------------------------

data AnomalySourceClass : Set where
  primaryEventCarrier
  boundedSecondaryReport
  familyReportedViaNews
  discoveryCommunityOnly
  unresolvedLocator : AnomalySourceClass

data AnomalyPaymentState : Set where
  primaryPaid
  boundedReportPaid
  discoveryOnly
  unpaid : AnomalyPaymentState

record ReportedAnomaly : Set where
  constructor reported-anomaly
  field
    person : String
    claim : String
    sourceClass : AnomalySourceClass
    paymentState : AnomalyPaymentState
    sourceURL : String
    whatIsActuallyPaid : String
    whatRemainsUnpaid : String
    nextPrimaryReceipt : String

open ReportedAnomaly public

casiasDeviceResetClaim : ReportedAnomaly
casiasDeviceResetClaim = reported-anomaly
  "Melissa Casias"
  "a personal phone was found at home factory-reset after her disappearance"
  familyReportedViaNews
  boundedReportPaid
  "https://www.kob.com/news/top-news/family-of-taos-woman-still-looking-for-her-a-month-after-disappearance/"
  "KOB directly attributes the factory-reset observation to Casias's family while reporting the disappearance chronology"
  "who initiated the reset, exact reset time, device/account telemetry, remote/local mechanism, motive and relevance to the death"
  "device forensic report, provider/account audit log, warrant return or law-enforcement digital-forensics report"

casiasGunshotMannerClaim : ReportedAnomaly
casiasGunshotMannerClaim = reported-anomaly
  "Melissa Casias"
  "autopsy found a gunshot wound to the head while manner remained undetermined"
  boundedSecondaryReport
  boundedReportPaid
  "https://www.latimes.com/world-nation/story/2026-08-18/unanswered-questions-continue-to-swirl-in-case-of-missing-new-mexico-los-alamos-lab-worker"
  "Los Angeles Times reports the New Mexico OMI cause/manner result and limitations from decomposition"
  "underlying autopsy/toxicology, range-of-fire evidence, weapon forensics, scene reconstruction and any eventual manner revision"
  "New Mexico Office of the Medical Investigator report plus law-enforcement scene/firearm reports"

chavezBilocationStatementClaim : ReportedAnomaly
chavezBilocationStatementClaim = reported-anomaly
  "Anthony Chavez"
  "a reported acquaintance/police-report statement says Chavez had been discussing how matter can exist in two places at once"
  discoveryCommunityOnly
  discoveryOnly
  "https://podcasts.apple.com/ie/podcast/irh-289-mkultra-reopened-1952-ufo-recording-biologics/id1530269237?i=1000776737055"
  "a current community/podcast manifestation repeats the claimed police-report content; it is retained only as a locator"
  "the exact police-report page, speaker identity/context, whether the wording is verbatim, and any relationship to a real scientific project or to Chavez's identity"
  "original missing-person/police report and authenticated interview statement; then same-person work/project receipt if any"

leblancAirportTelemetryClaim : ReportedAnomaly
leblancAirportTelemetryClaim = reported-anomaly
  "Joshua Kyle LeBlanc"
  "reporting says Tesla Sentry Mode/location data placed his vehicle at Huntsville International Airport for about four hours before the fatal crash"
  boundedSecondaryReport
  boundedReportPaid
  "https://www.foxnews.com/us/nasa-nuclear-engineer-found-dead-burned-tesla-vanishing-alabama-home-last-year/"
  "Fox News reports the approximately four-hour airport stop and attributes vehicle tracing to Tesla Sentry Mode data"
  "raw Tesla telemetry, video, account/cloud records, who occupied/drove the vehicle, exact timestamps and causal significance"
  "law-enforcement crash file plus authenticated Tesla telemetry/video export and chain of custody"

mccaslandSpaceForceMeetingClaim : ReportedAnomaly
mccaslandSpaceForceMeetingClaim = reported-anomaly
  "William Neil McCasland"
  "online reporting claims a specific Space Force meeting shortly before disappearance"
  unresolvedLocator
  unpaid
  ""
  "nothing beyond a search lead; a 2021 AFRL public photograph independently establishes historical Space Force ceremonial adjacency, not a 2026 meeting"
  "date, attendees, purpose, event-time identity, meeting record and any connection to disappearance"
  "official calendar, visitor/meeting log, authenticated photograph metadata/bodycam, attendee statement or released investigative record"

rezaSearchGeometryClaim : ReportedAnomaly
rezaSearchGeometryClaim = reported-anomaly
  "Monica Jacinto Reza"
  "secondary reporting describes disappearance during a Mount Waterman hike, extensive searches and a recovered beanie; some commentary proposes a staged/intercepted disappearance"
  boundedSecondaryReport
  boundedReportPaid
  "https://lamag.com/crimeinla/missing-nasa-scientist-monica-reza-geo-profiler-suggests-possible-staged-disappearance/"
  "the publication pays its own reported search/event narrative and the existence of the profiler hypothesis"
  "staging/interception, exact last-seen geometry, scent-track interpretation, beanie identity/chain of custody and any work-related cause"
  "Los Angeles County Sheriff search report, SAR logs/GPS tracks, evidence-property record and witness statements"

record AnomalyAttributionBoundary : Set where
  constructor anomaly-attribution-boundary
  field
    secondaryReportDoesNotBecomePrimaryEventFact : Bool
    familyStatementDoesNotBecomeForensicFinding : Bool
    communityLocatorMayNominatePrimarySearch : Bool
    unexplainedObservationCreatesCommonCause : Bool
    exactUnderlyingCarrierNeededForPromotion : Bool

canonicalAnomalyAttributionBoundary : AnomalyAttributionBoundary
canonicalAnomalyAttributionBoundary = anomaly-attribution-boundary
  true true true false true

secondaryReportDoesNotBecomePrimaryEventFact : Bool
secondaryReportDoesNotBecomePrimaryEventFact = true

sourceAtlasPresent :
  Sources.investigativeSourceAtlas ≡ Sources.investigativeSourceAtlas
sourceAtlasPresent = refl
