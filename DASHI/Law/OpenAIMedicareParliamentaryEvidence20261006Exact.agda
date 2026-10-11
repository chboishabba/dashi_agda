module DASHI.Law.OpenAIMedicareParliamentaryEvidence20261006Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Law.AIHumanCorporateAttributionSensibLaw2026Exact as Bridge
import DASHI.Law.AustralianCommonwealthAgentComputerOffenceAttribution2026Exact as Cth

------------------------------------------------------------------------
-- 6 OCTOBER 2026 PARLIAMENTARY-HEARING EVIDENCE BOUNDARY
--
-- Public reporting of OpenAI CSO Jason Kwon's evidence supplies post-incident
-- organisational-response facts and an acknowledgement that notification should
-- have occurred sooner.  It does not supply the unreleased June execution trace
-- or establish pre-incident intention, knowledge, authorisation or corporate
-- fault for the s 478.1 candidate offence.
------------------------------------------------------------------------

record HearingSource : Set where
  constructor hearingSource
  field
    publisher : String
    title : String
    publishedDate : String
    url : String
    sourceRole : String

open HearingSource public

abcKeyTakeaways20261006 : HearingSource
abcKeyTakeaways20261006 = hearingSource
  "ABC News"
  "OpenAI executive flew to Australia to apologise over Medicare hack. Here are the key takeaways"
  "2026-10-06"
  "https://www.abc.net.au/news/2026-10-06/openai-hearing-apology-key-takeaways/107235640"
  "secondary public report of parliamentary evidence"

abcPoliticsLive20261006 : HearingSource
abcPoliticsLive20261006 = hearingSource
  "ABC News"
  "Federal politics: AI execs pledge quicker warnings of rogue agent hacks — as it happened"
  "2026-10-06"
  "https://www.abc.net.au/news/2026-10-06/federal-politics-live-blog-coalition-migration-oct-6/107230622"
  "secondary contemporaneous report carrying hearing statements"

record ParliamentaryResponseEvidence : Set where
  constructor parliamentaryResponseEvidence
  field
    parliamentaryAppearanceReported : Bool
    apologyReported : Bool
    delayedNotificationAcknowledged : Bool
    postIncidentMonitoringEstablished : Bool
    realTimeInternetUseAlertReported : Bool
    laterIncidentFasterNotificationReported : Bool
    someStaffKnowledgeBeforeSep1Reported : Bool
    chiefExecutiveKnowledgeBeforeSep1Established : Bool
    preIncidentKnowledgeNotEstablished : Bool
    juneRuntimeTraceReleased : Bool
    juneMensReaEstablished : Bool
    corporateFaultForJuneEstablished : Bool

open ParliamentaryResponseEvidence public

openAIParliamentaryResponseEvidence : ParliamentaryResponseEvidence
openAIParliamentaryResponseEvidence = parliamentaryResponseEvidence
  true true true true true true true false true false false false

postIncidentMonitoringEstablished :
  ParliamentaryResponseEvidence.postIncidentMonitoringEstablished
    openAIParliamentaryResponseEvidence ≡ true
postIncidentMonitoringEstablished = refl

delayedNotificationAcknowledged :
  ParliamentaryResponseEvidence.delayedNotificationAcknowledged
    openAIParliamentaryResponseEvidence ≡ true
delayedNotificationAcknowledged = refl

preIncidentKnowledgeNotEstablished :
  ParliamentaryResponseEvidence.preIncidentKnowledgeNotEstablished
    openAIParliamentaryResponseEvidence ≡ true
preIncidentKnowledgeNotEstablished = refl

------------------------------------------------------------------------
-- Temporal / evidentiary firewalls.
------------------------------------------------------------------------

data RemedialMeasuresImplyPriorFaultPermission : Set where
data PostIncidentKnowledgeImpliesJuneMensReaPermission : Set where
data DelayedNotificationImpliesUnderlyingOffencePermission : Set where
data ApologyImpliesLegalAdmissionPermission : Set where

remedialMeasuresDoNotAutoProvePriorFault :
  RemedialMeasuresImplyPriorFaultPermission → ⊥
remedialMeasuresDoNotAutoProvePriorFault ()

postIncidentKnowledgeDoesNotAutoProveJuneMensRea :
  PostIncidentKnowledgeImpliesJuneMensReaPermission → ⊥
postIncidentKnowledgeDoesNotAutoProveJuneMensRea ()

delayedNotificationDoesNotAutoProveUnderlyingOffence :
  DelayedNotificationImpliesUnderlyingOffencePermission → ⊥
delayedNotificationDoesNotAutoProveUnderlyingOffence ()

apologyDoesNotAutoBecomeLegalAdmission :
  ApologyImpliesLegalAdmissionPermission → ⊥
apologyDoesNotAutoBecomeLegalAdmission ()

------------------------------------------------------------------------
-- Cross-owner consistency receipts.
------------------------------------------------------------------------

existingMedicareTraceStillOpen :
  Bridge.exactRuntimeTraceAvailable Bridge.medicareLegalAttributionBoundary ≡ false
existingMedicareTraceStillOpen = Bridge.medicareTraceStillNotGrounded

existingMedicareMensReaStillOpen :
  Bridge.mensReaEstablished Bridge.medicareLegalAttributionBoundary ≡ false
existingMedicareMensReaStillOpen = Bridge.medicareMensReaStillOpen

existing4781OffenceStillOpen :
  Cth.offenceEstablished Cth.medicare4781ApplicationBoundary ≡ false
existing4781OffenceStillOpen = refl

hearingBoundary : String
hearingBoundary =
  "The 6 October hearing materially advances the post-incident response record: apology, delayed-notification acknowledgement, real-time monitoring/alerts and faster later notification are publicly reported. Those later facts do not establish the June execution trace, pre-incident knowledge, s 478.1 intention/knowledge, statutory employee/agent/officer attribution, corporate authorisation or criminal liability."
