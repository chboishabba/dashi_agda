module DASHI.Cognition.PNF.SensibLawEventTimeLegalSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority

------------------------------------------------------------------------
-- EVENT-TIME LEGAL-SOURCE AUTHORITY
--
-- LegalSourceAuthorityReceiptInState records a source as validityCurrent but
-- does not index that validity to a date.  Historical matters need a stronger
-- consumer-relative receipt: the exact source used by the legal meet must be
-- shown operative at the event date under an explicit legislative interval.
--
-- This wrapper does not replace the existing authority owner.  It refines it
-- for historical consumers and deliberately does not infer present-day
-- validity from validity at the historical event time (or vice versa).
------------------------------------------------------------------------

record EventTimeLegalSourceAuthorityReceipt
    {state : Status.SemanticCommitmentState}
    (authority : Authority.LegalSourceAuthorityReceiptInState state) : Set₁ where
  constructor event-time-legal-source-authority-receipt
  field
    eventDate : String
    intervalEffectiveFrom : String
    nextVersionEffectiveFrom : String
    eventFallsWithinInterval : Set

    exactProvisionLocator : String
    officialPointInTimeSourceReference : String
    officialLegislativeHistoryReference : String

    exactAuthoritySource : Ontology.LegalSource
    exactAuthoritySourceIsMeetSource :
      exactAuthoritySource ≡ Authority.source authority

    sourceOperativeAtEventTime : Bool
    sourceOperativeAtEventTimeIsTrue : sourceOperativeAtEventTime ≡ true

    eventTimeValidityUsesExactSourceIdentity : Bool
    eventTimeValidityUsesExactSourceIdentityIsTrue :
      eventTimeValidityUsesExactSourceIdentity ≡ true

    presentDayValidityAssessed : Bool
    presentDayValidityAssessedIsFalse : presentDayValidityAssessed ≡ false

    receiptReference : String

open EventTimeLegalSourceAuthorityReceipt public

------------------------------------------------------------------------
-- The exact historical source can be projected back to the existing meet
-- source, but the temporal payment remains a separate consumer-relative fibre.
------------------------------------------------------------------------

eventTimeAuthorityUsesExactMeetSource :
  ∀ {state}
    {authority : Authority.LegalSourceAuthorityReceiptInState state} →
  (receipt : EventTimeLegalSourceAuthorityReceipt authority) →
  exactAuthoritySource receipt ≡ Authority.source authority
eventTimeAuthorityUsesExactMeetSource = exactAuthoritySourceIsMeetSource

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data UnindexedCurrentValidityPaysHistoricalValidity : Set where
data HistoricalValidityProvesPresentValidity : Set where
data PresentValidityProvesHistoricalValidity : Set where
data SameCitationProvesSameHistoricalSource : Set where
data EventTimeAuthorityAloneProvesApplicability : Set where

unindexedCurrentValidityDoesNotPayHistoricalValidity :
  UnindexedCurrentValidityPaysHistoricalValidity → ⊥
unindexedCurrentValidityDoesNotPayHistoricalValidity ()

historicalValidityDoesNotProvePresentValidity :
  HistoricalValidityProvesPresentValidity → ⊥
historicalValidityDoesNotProvePresentValidity ()

presentValidityDoesNotProveHistoricalValidity :
  PresentValidityProvesHistoricalValidity → ⊥
presentValidityDoesNotProveHistoricalValidity ()

sameCitationDoesNotProveSameHistoricalSource :
  SameCitationProvesSameHistoricalSource → ⊥
sameCitationDoesNotProveSameHistoricalSource ()

eventTimeAuthorityDoesNotProveApplicability :
  EventTimeAuthorityAloneProvesApplicability → ⊥
eventTimeAuthorityDoesNotProveApplicability ()

record EventTimeLegalSourceAuthorityBoundary : Set where
  constructor event-time-legal-source-authority-boundary
  field
    eventDateIndexed : Bool
    explicitVersionIntervalRequired : Bool
    exactProvisionLocatorRequired : Bool
    officialPointInTimeSourceRequired : Bool
    officialLegislativeHistoryRequired : Bool
    exactMeetSourceWeldRequired : Bool
    sourceOperativeAtEventTimeRequired : Bool
    unindexedCurrentValidityPaysHistoricalValidity : Bool
    historicalValidityProvesPresentValidity : Bool
    presentValidityProvesHistoricalValidity : Bool
    sameCitationProvesSameHistoricalSource : Bool
    eventTimeAuthorityAloneProvesApplicability : Bool

canonicalEventTimeLegalSourceAuthorityBoundary :
  EventTimeLegalSourceAuthorityBoundary
canonicalEventTimeLegalSourceAuthorityBoundary =
  event-time-legal-source-authority-boundary
    true true true true true true true
    false false false false false
