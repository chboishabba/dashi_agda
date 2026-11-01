module DASHI.Core.EventTimeCapabilityAlignmentBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EVENT-TIME CAPABILITY ALIGNMENT, BIDI
--
-- Historical expertise, title, clearance or programme participation is not the
-- same proposition as event-time possession/access to a capability-bearing
-- application transformation.
------------------------------------------------------------------------

data TemporalRelation : Set where
  historicalOnly : TemporalRelation
  recentPreEvent : TemporalRelation
  eventTime : TemporalRelation
  postEvent : TemporalRelation
  unresolvedTime : TemporalRelation


record EventTimeCapabilityReceipt : Set where
  constructor event-time-capability-receipt
  field
    personOrRole : String
    applicationObject : String
    relation : TemporalRelation
    sourceReference : String
    boundedReading : String

open EventTimeCapabilityReceipt public

data EventTimeReverseTarget : Set where
  acquireLastKnownActiveRole : EventTimeReverseTarget
  acquireLastKnownAccess : EventTimeReverseTarget
  acquireCurrentProjectAssignment : EventTimeReverseTarget
  acquireCurrentConfigurationOwnership : EventTimeReverseTarget
  acquireCurrentDecisionOrReviewRole : EventTimeReverseTarget
  acquireAccessRevocationOrTransfer : EventTimeReverseTarget
  acquireDepartureOrReassignmentDate : EventTimeReverseTarget
  acquireEventTimeSuccessor : EventTimeReverseTarget


record EventTimeAlignmentBoundary : Set where
  constructor event-time-alignment-boundary
  field
    historicalExpertiseImpliesEventTimePossession : Bool
    historicalExpertiseImpliesEventTimePossessionIsFalse : historicalExpertiseImpliesEventTimePossession ≡ false
    historicalClearanceImpliesCurrentAccess : Bool
    historicalClearanceImpliesCurrentAccessIsFalse : historicalClearanceImpliesCurrentAccess ≡ false
    publicationBeforeEventImpliesCurrentOperationalRole : Bool
    publicationBeforeEventImpliesCurrentOperationalRoleIsFalse : publicationBeforeEventImpliesCurrentOperationalRole ≡ false
    recentRoleCanPrioritiseEventTimeSearch : Bool
    recentRoleCanPrioritiseEventTimeSearchIsTrue : recentRoleCanPrioritiseEventTimeSearch ≡ true

canonicalEventTimeAlignmentBoundary : EventTimeAlignmentBoundary
canonicalEventTimeAlignmentBoundary = event-time-alignment-boundary false refl false refl false refl true refl
