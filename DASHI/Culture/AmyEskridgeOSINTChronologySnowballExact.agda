module DASHI.Culture.AmyEskridgeOSINTChronologySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeOSINTSnowballExact as OSINT
import DASHI.Culture.AmyEskridgeMessageProvenanceBacktraceExact as Message
import DASHI.Culture.AmyEskridgeDemiseCircumstancesSnowballExact as Demise

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: DATED OSINT CHRONOLOGY SNOWBALL
--
-- Chronology is an ordering surface, not a causal model.  Dates are admitted
-- only at the precision supported by the source carrier.  Reported messages
-- remain source-of-source leads until native/authenticated carriers are paid.
------------------------------------------------------------------------

data DatePrecision : Set where
  exactDay : DatePrecision
  monthOnly : DatePrecision
  relativeWindow : DatePrecision
  dateUnresolved : DatePrecision

data ChronologyRole : Set where
  firstPersonHistoricalStatement : ChronologyRole
  reportedPrivateCorrespondence : ChronologyRole
  memorialDeathDate : ChronologyRole
  obituaryPublication : ChronologyRole
  laterOSINTPublication : ChronologyRole
  institutionalReviewContext : ChronologyRole

data CarrierStrength : Set where
  exactPublicCarrier : CarrierStrength
  archivedSpeakerCarrier : CarrierStrength
  sourceOfSourceLead : CarrierStrength
  institutionalPrimaryCarrier : CarrierStrength
  secondaryReportingCarrier : CarrierStrength

record ChronologyAtom : Set where
  constructor chronology-atom
  field
    dateLabel : String
    precision : DatePrecision
    role : ChronologyRole
    carrierStrength : CarrierStrength
    sourceReference : String
    eventSummary : String
    exactEventDatePaid : Bool
    exactCarrierIdentityPaid : Bool
    authorshipOrSpeakerIdentityPaid : Bool
    propositionSupportPaid : Bool
    createsCausalLink : Bool
    createsDeathMannerFinding : Bool
    createsActorIdentityFinding : Bool

open ChronologyAtom public

------------------------------------------------------------------------
-- Pre-death first-person intrusion account.
-- The archive supports that Amy made the statement; the underlying apartment
-- event dates are not recovered from this carrier.
------------------------------------------------------------------------

intrusionStatementChronology : ChronologyAtom
intrusionStatementChronology = chronology-atom
  "date unresolved; statement describes an earlier six-month apartment period"
  dateUnresolved
  firstPersonHistoricalStatement
  archivedSpeakerCarrier
  "Blocked Epistemology archive, Amy Eskridge Zoom, approximately 38:07 onward"
  "Amy reports repeated apartment entries while she and her then-partner were absent and describes the cut micro-USB charger; exact incident dates remain unresolved."
  false true true true false false false

------------------------------------------------------------------------
-- Reported May 2022 correspondence.
-- These dates are source-attributed to secondary/public Milburn reporting and
-- do not yet carry native-message authentication.
------------------------------------------------------------------------

may13ReportedNonSuicideMessage : ChronologyAtom
may13ReportedNonSuicideMessage = chronology-atom
  "2022-05-13"
  exactDay
  reportedPrivateCorrespondence
  sourceOfSourceLead
  "Hindustan Times / Daily Mail / Franc Milburn reporting chain"
  "Secondary reporting attributes to Amy a May 13 message denying that a future suicide, overdose, or killing report would be genuine."
  true false false true false false false

may19ReportedDirectedEnergyMessage : ChronologyAtom
may19ReportedDirectedEnergyMessage = chronology-atom
  "2022-05-19"
  exactDay
  reportedPrivateCorrespondence
  sourceOfSourceLead
  "Milburn-reporting chain; later public articles reproduce the reported date/content"
  "Secondary reporting attributes to Amy a May 19 message describing burns and relaying another person's interpretation involving an RF K-band emitter; neither the message nor the claimed device is independently authenticated here."
  true false false true false false false

------------------------------------------------------------------------
-- Death and memorial publication.
------------------------------------------------------------------------

deathDateChronology : ChronologyAtom
deathDateChronology = chronology-atom
  "2022-06-11"
  exactDay
  memorialDeathDate
  exactPublicCarrier
  "AL.com / Legacy family obituary"
  "Family obituary states Amy Catherine Eskridge died Saturday, June 11, 2022, aged 34; it does not state cause or manner."
  true true true true false false false

obituaryPublicationChronology : ChronologyAtom
obituaryPublicationChronology = chronology-atom
  "2022-06-21 through 2022-06-26"
  relativeWindow
  obituaryPublication
  exactPublicCarrier
  "AL.com obituary publication window"
  "The family obituary was published by AL.com from June 21 through June 26, 2022."
  true true true true false false false

------------------------------------------------------------------------
-- 2026 OSINT / institutional review context remains post-event evidence.
------------------------------------------------------------------------

houseReviewChronology : ChronologyAtom
houseReviewChronology = chronology-atom
  "2026-04-20"
  exactDay
  institutionalReviewContext
  institutionalPrimaryCarrier
  "U.S. House Committee on Oversight and Government Reform letter dated April 20, 2026"
  "The House committee requested agency briefings concerning unconfirmed reports about deaths/disappearances involving sensitive scientific personnel; this is broader review context, not an Amy-specific forensic finding."
  true true true true false false false

milburnPublicPostChronology : ChronologyAtom
milburnPublicPostChronology = chronology-atom
  "2026-04-27"
  exactDay
  laterOSINTPublication
  sourceOfSourceLead
  "Franc Milburn public X-post lead referenced/embedded by downstream articles"
  "A later public Milburn post is a closer-to-origin carrier for the reported Amy correspondence, but it remains distinct from native message export and device/account metadata."
  true false false false false false false

------------------------------------------------------------------------
-- Cross-owner alignment.
------------------------------------------------------------------------

deathDateMatchesDemiseAtom :
  Demise.proposition Demise.familyObituaryDateAtom ≡ Demise.dateOfDeath
deathDateMatchesDemiseAtom = refl

reportedMessageMatchesOSINTAtom :
  OSINT.proposition OSINT.reportedNonSuicideMessageLeadAtom ≡
    OSINT.reportedPreDeathNonSuicideStatement
reportedMessageMatchesOSINTAtom = refl

publicMilburnStageStillNotAuthenticated :
  Message.status Message.milburnPublicPostStage ≡ Message.publicLeadLocated
publicMilburnStageStillNotAuthenticated = refl

------------------------------------------------------------------------
-- Chronology firewalls.
------------------------------------------------------------------------

record ChronologyBoundary : Set where
  constructor chronology-boundary
  field
    temporalOrderingCreatesCausation : Bool
    exactReportedDateEqualsNativeMessageAuthentication : Bool
    firstPersonStatementDateEqualsUnderlyingIncidentDate : Bool
    laterPublicationBackdatesCarrierAuthentication : Bool
    preDeathWarningDeterminesDeathManner : Bool
    reportedDirectedEnergyClaimEstablishesDirectedEnergyAttack : Bool
    post2026ReviewEstablishes2022CaseConnection : Bool
    chronologyMayExposeContradictionsAndAcquisitionGaps : Bool
    unresolvedDatesRemainExplicit : Bool

canonicalChronologyBoundary : ChronologyBoundary
canonicalChronologyBoundary = chronology-boundary
  false false false false false false false true true
