module DASHI.Culture.MissingDeceasedEventTimeStreamsBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Social.StreamsEngineBoundary as S
import DASHI.Core.EventTimeOperationalPossessionEvidenceExact as E

------------------------------------------------------------------------
-- VALID-TIME / OBSERVED-TIME BRIDGE FOR EVENT-TIME POSSESSION
--
-- Reuses the older Streams Engine provenance semantics rather than introducing
-- another temporal model. A source may be observed/published later than the
-- role/access interval it describes; conversely a later retrospective statement
-- does not itself establish that the asserted role was valid at event time.
------------------------------------------------------------------------

record EventTimeSourceAnchorReceipt : Set where
  constructor event-time-source-anchor-receipt
  field
    subject : String
    carrier : String
    eventDate : String
    anchor : S.SourceAnchor
    evidenceKind : E.ContinuityEvidenceKind
    validTimeSupportsEventWindow : Bool
    observedTimeDistinctFromValidTime : Bool
    boundedReading : String

open EventTimeSourceAnchorReceipt public

record EventTimeStreamsBoundary : Set where
  constructor event-time-streams-boundary
  field
    observedAfterEventImpliesValidAtEvent : Bool
    observedAfterEventImpliesValidAtEventIsFalse :
      observedAfterEventImpliesValidAtEvent ≡ false
    publicationDateImpliesRoleValidTime : Bool
    publicationDateImpliesRoleValidTimeIsFalse :
      publicationDateImpliesRoleValidTime ≡ false
    temporalAlignmentImpliesOperationalPossession : Bool
    temporalAlignmentImpliesOperationalPossessionIsFalse :
      temporalAlignmentImpliesOperationalPossession ≡ false
    eventTimePossessionImpliesEventCausation : Bool
    eventTimePossessionImpliesEventCausationIsFalse :
      eventTimePossessionImpliesEventCausation ≡ false
    validTimeAnchoredSameCarrierUseCanSupportEventTimePossession : Bool
    validTimeAnchoredSameCarrierUseCanSupportEventTimePossessionIsTrue :
      validTimeAnchoredSameCarrierUseCanSupportEventTimePossession ≡ true

canonicalEventTimeStreamsBoundary : EventTimeStreamsBoundary
canonicalEventTimeStreamsBoundary = event-time-streams-boundary
  false refl
  false refl
  false refl
  false refl
  true refl

data EventTimeTemporalReverseTarget : Set where
  acquireValidTimeAnchor : EventTimeTemporalReverseTarget
  acquireObservedTimeAnchor : EventTimeTemporalReverseTarget
  acquireEventWindowOverlap : EventTimeTemporalReverseTarget
  acquireSameCarrierOperationalUseAtValidTime : EventTimeTemporalReverseTarget
