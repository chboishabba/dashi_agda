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
-- QCAT pp.82-83 and source-native court-bundle events dated 24 and 28 February
-- 2022.  Only aggregate relation receipts are public here; no physiological
-- values or private note text are committed.
--
-- Processing owner:
--   scripts/process_sensiblaw_health_evidence.py
--   contract sensiblaw-health-evidence-v2
--   join granularity = source-row
--   event precision = day
------------------------------------------------------------------------

privateDatasetDigest : String
privateDatasetDigest = Private.privateTranscriptionDigestSha256

privateDatasetReference : String
privateDatasetReference = Private.privateTranscriptionArtifactReference

processorContract : String
processorContract = Processor.processorContractVersion

------------------------------------------------------------------------
-- Court-source event fibres.
------------------------------------------------------------------------

data RussellEventId : Set where
  entryNotice24Feb : RussellEventId
  textMessage24Feb : RussellEventId
  clarificationRequest24Feb : RussellEventId
  issuesNotice24Feb : RussellEventId
  issuesResponse24Feb : RussellEventId
  repairs28Feb : RussellEventId
  vacatingRequirements28Feb : RussellEventId

record RussellDayEvent : Set₁ where
  constructor russellDayEvent
  field
    eventId : RussellEventId
    dateReference : String
    sourceReference : String
    sourceReceipt : Set

open RussellDayEvent public

entryNoticeEvent : Set → RussellDayEvent
entryNoticeEvent r = russellDayEvent entryNotice24Feb "2022-02-24" "QCAT final bundle: 24/02/2022 Entry Notice - Caton" r

textMessageEvent : Set → RussellDayEvent
textMessageEvent r = russellDayEvent textMessage24Feb "2022-02-24" "QCAT final bundle: 24/02/2022 Text message - Caton" r

clarificationRequestEvent : Set → RussellDayEvent
clarificationRequestEvent r = russellDayEvent clarificationRequest24Feb "2022-02-24" "QCAT final bundle: 24/02/2022 Request for clarification of issues to be attended to - Brown" r

issuesNoticeEvent : Set → RussellDayEvent
issuesNoticeEvent r = russellDayEvent issuesNotice24Feb "2022-02-24" "QCAT final bundle: 24/02/2022 Notice of Issues to be attended to - Caton" r

issuesResponseEvent : Set → RussellDayEvent
issuesResponseEvent r = russellDayEvent issuesResponse24Feb "2022-02-24" "QCAT final bundle: 24/02/2022 Response to Issues requiring attention - Brown" r

repairsEvent : Set → RussellDayEvent
repairsEvent r = russellDayEvent repairs28Feb "2022-02-28" "QCAT final bundle: 28/02/2022 Repairs - Caton" r

vacatingRequirementsEvent : Set → RussellDayEvent
vacatingRequirementsEvent r = russellDayEvent vacatingRequirements28Feb "2022-02-28" "QCAT final bundle: 28/02/2022 Requirements of Vacating Premises - Caton" r

russellEvents : Set → List RussellDayEvent
russellEvents r =
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
    pairwiseJoinCountReference : String
    afterCountReference : String
    beforeCountReference : String
    sameDayCountReference : String
    sameDayRowsPer24FebEventReference : String
    sameDayRowsPer28FebEventReference : String
    eventPrecision : Processor.EventPrecision
    joinGranularity : Processor.JoinGranularity
    processorExecutionReceipt : Set
    eventSourceReceipt : Set

open RussellHealthEventJoinReceipt public

russellHealthEventJoinReceipt :
  (processorExecutionReceipt : Set) →
  (eventSourceReceipt : Set) →
  RussellHealthEventJoinReceipt
russellHealthEventJoinReceipt processorExecutionReceipt eventSourceReceipt =
  russellHealthEventJoinReceipt
    processorContract
    privateDatasetDigest
    "89 private source rows"
    "87 parseable source-row timestamps"
    "2 unresolved source-row timestamps"
    "7 source-native day-precision Russell events"
    "609 pairwise source-row/event relations"
    "466 after relations"
    "92 before relations"
    "51 same-day relations"
    "5 same-day source rows for each 24-Feb event"
    "13 same-day source rows for each 28-Feb event"
    Processor.dayPrecision
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
