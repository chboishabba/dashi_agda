module DASHI.Law.SensibLawRussellHealthEventJoin20220223_0303Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
import DASHI.Interop.SensibLawHealthEvidenceProcessorParityExact as Processor
import DASHI.Law.SensibLawQCATHealthPages82_83PrivateDatasetFixtureExact as Private

------------------------------------------------------------------------
-- RUSSELL / QCAT 0096/22 HEALTH-EVENT TEMPORAL JOIN
--
-- Privacy-safe regression over the complete 89-row private transcription of
-- QCAT pp.82-83 and source-native Russell/tenancy events dated 23, 24 and 28
-- February 2022. Only aggregate relation receipts are public here; no
-- physiological values or private note text are committed.
--
-- Processing owner:
--   scripts/process_sensiblaw_health_evidence.py
--   contract sensiblaw-health-evidence-v2
--   join granularity = source-row
------------------------------------------------------------------------

privateDatasetDigest : String
privateDatasetDigest = Private.privateTranscriptionDigestSha256

privateDatasetReference : String
privateDatasetReference = Private.privateTranscriptionArtifactReference

processorContract : String
processorContract = Processor.processorContractVersion

------------------------------------------------------------------------
-- Source-native event fibres.
------------------------------------------------------------------------

data RussellEventId : Set where
  sequrRetaliativeEviction23Feb : RussellEventId
  entryNotice24Feb : RussellEventId
  textMessage24Feb : RussellEventId
  clarificationRequest24Feb : RussellEventId
  issuesNotice24Feb : RussellEventId
  issuesResponse24Feb : RussellEventId
  repairs28Feb : RussellEventId
  vacatingRequirements28Feb : RussellEventId

record RussellEvent : Set₁ where
  constructor russellEvent
  field
    eventId : RussellEventId
    eventTimeReference : String
    eventPrecision : Processor.EventPrecision
    sourceReference : String
    sourceReceipt : Set

open RussellEvent public

sequrEvent : Set → RussellEvent
sequrEvent r =
  russellEvent
    sequrRetaliativeEviction23Feb
    "2022-02-23T09:44:13+10:00"
    Processor.timestampPrecision
    "Gmail: SEQUR 'Retaliative Eviction' correspondence; QSTARS/contesting eviction notice"
    r

entryNoticeEvent : Set → RussellEvent
entryNoticeEvent r = russellEvent entryNotice24Feb "2022-02-24" Processor.dayPrecision "QCAT final bundle: 24/02/2022 Entry Notice - Caton" r

textMessageEvent : Set → RussellEvent
textMessageEvent r = russellEvent textMessage24Feb "2022-02-24" Processor.dayPrecision "QCAT final bundle: 24/02/2022 Text message - Caton" r

clarificationRequestEvent : Set → RussellEvent
clarificationRequestEvent r = russellEvent clarificationRequest24Feb "2022-02-24" Processor.dayPrecision "QCAT final bundle: 24/02/2022 Request for clarification of issues to be attended to - Brown" r

issuesNoticeEvent : Set → RussellEvent
issuesNoticeEvent r = russellEvent issuesNotice24Feb "2022-02-24" Processor.dayPrecision "QCAT final bundle: 24/02/2022 Notice of Issues to be attended to - Caton" r

issuesResponseEvent : Set → RussellEvent
issuesResponseEvent r = russellEvent issuesResponse24Feb "2022-02-24" Processor.dayPrecision "QCAT final bundle: 24/02/2022 Response to Issues requiring attention - Brown" r

repairsEvent : Set → RussellEvent
repairsEvent r = russellEvent repairs28Feb "2022-02-28" Processor.dayPrecision "QCAT final bundle: 28/02/2022 Repairs - Caton" r

vacatingRequirementsEvent : Set → RussellEvent
vacatingRequirementsEvent r = russellEvent vacatingRequirements28Feb "2022-02-28" Processor.dayPrecision "QCAT final bundle: 28/02/2022 Requirements of Vacating Premises - Caton" r

russellEvents : Set → List RussellEvent
russellEvents r =
  sequrEvent r ∷
  entryNoticeEvent r ∷
  textMessageEvent r ∷
  clarificationRequestEvent r ∷
  issuesNoticeEvent r ∷
  issuesResponseEvent r ∷
  repairsEvent r ∷
  vacatingRequirementsEvent r ∷ []

------------------------------------------------------------------------
-- Exact aggregate processor receipt from the private source-row join.
------------------------------------------------------------------------

record RussellHealthEventJoinReceipt : Set₁ where
  constructor russellHealthEventJoinReceipt
  field
    processorContractReference : String
    privateDatasetDigestReference : String
    privateSourceRowCountReference : String
    parseableSourceRowCountReference : String
    unresolvedSourceRowCountReference : String
    eventCountReference : String
    eventPrecisionProfileReference : String
    pairwiseJoinCountReference : String
    afterCountReference : String
    beforeCountReference : String
    sameDayCountReference : String
    sameDayRows23FebReference : String
    sameDayRowsPer24FebEventReference : String
    sameDayRowsPer28FebEventReference : String
    joinGranularity : Processor.JoinGranularity
    processorExecutionReceipt : Set
    eventSourceReceipt : Set

open RussellHealthEventJoinReceipt public

canonicalRussellHealthEventJoinReceipt :
  (processorExecutionReceipt : Set) →
  (eventSourceReceipt : Set) →
  RussellHealthEventJoinReceipt
canonicalRussellHealthEventJoinReceipt processorExecutionReceipt eventSourceReceipt =
  russellHealthEventJoinReceipt
    processorContract
    privateDatasetDigest
    "89 private source rows"
    "87 parseable source-row timestamps"
    "2 unresolved source-row timestamps"
    "8 source-native Russell/tenancy events"
    "1 exact-timestamp Gmail event + 7 day-precision QCAT-bundle events"
    "696 pairwise source-row/event relations"
    "547 after relations"
    "93 before relations"
    "56 same-day relations"
    "5 same-day source rows for the 23-Feb SEQUR event"
    "5 same-day source rows for each 24-Feb event"
    "13 same-day source rows for each 28-Feb event"
    Processor.sourceRowGranularity
    processorExecutionReceipt
    eventSourceReceipt

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record RussellHealthEventJoinBoundary : Set where
  constructor russellHealthEventJoinBoundary
  field
    sameDayAutomaticallyCausal : Bool
    sameDayAutomaticallyCausalIsFalse : sameDayAutomaticallyCausal ≡ false
    afterAutomaticallyCausal : Bool
    afterAutomaticallyCausalIsFalse : afterAutomaticallyCausal ≡ false
    pairwiseJoinCountEqualsIndependentEvidenceCount : Bool
    pairwiseJoinCountEqualsIndependentEvidenceCountIsFalse :
      pairwiseJoinCountEqualsIndependentEvidenceCount ≡ false
    sourceRowJoinMayMultiplyByMetricCount : Bool
    sourceRowJoinMayMultiplyByMetricCountIsFalse :
      sourceRowJoinMayMultiplyByMetricCount ≡ false
    dayPrecisionMayInventExactClockTime : Bool
    dayPrecisionMayInventExactClockTimeIsFalse :
      dayPrecisionMayInventExactClockTime ≡ false
    unresolvedTimestampMayBeSilentlyRepaired : Bool
    unresolvedTimestampMayBeSilentlyRepairedIsFalse :
      unresolvedTimestampMayBeSilentlyRepaired ≡ false
    temporalJoinAutomaticallyIdentifiesParticularHarm : Bool
    temporalJoinAutomaticallyIdentifiesParticularHarmIsFalse :
      temporalJoinAutomaticallyIdentifiesParticularHarm ≡ false

canonicalRussellHealthEventJoinBoundary : RussellHealthEventJoinBoundary
canonicalRussellHealthEventJoinBoundary =
  russellHealthEventJoinBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
