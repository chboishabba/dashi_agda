module DASHI.Culture.LoureiroEventAlternativeEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LOUREIRO EVENT-SPECIFIC ALTERNATIVE EVIDENCE
--
-- MIT's 19 Dec 2025 statement says authorities identified the same individual
-- as responsible for Professor Nuno Loureiro's killing and the Brown University
-- mass shooting.  This is event-specific evidence independent of Loureiro's
-- fusion/plasma work and therefore must be represented as competing pressure
-- against any science-targeting explanation.
------------------------------------------------------------------------

data EventAlternativeStatus : Set where
  institutionalSourceBacked
  partial
  notLocated
  : EventAlternativeStatus

record EventAlternativeReceipt : Set where
  constructor event-alternative-receipt
  field
    person : String
    proposition : String
    status : EventAlternativeStatus
    sourceReference : String
    boundedReading : String

open EventAlternativeReceipt public

sameSuspectAsBrownShooting : EventAlternativeReceipt
sameSuspectAsBrownShooting = event-alternative-receipt
  "Nuno F. G. Loureiro"
  "authorities linked the suspect in Loureiro's killing to the Brown University mass shooting"
  institutionalSourceBacked
  "MIT News, Statement on Professor Nuno Loureiro, 19 Dec 2025"
  "This is strong event-specific evidence of a broader violent-event connection. It does not by itself establish motive, but it materially weakens any inference from Loureiro's scientific importance to a science-specific targeting explanation."

record LoureiroEventAlternativeBoundary : Set where
  constructor loureiro-event-alternative-boundary
  field
    sameSuspectLinkEstablishesMotive : Bool
    sameSuspectLinkEstablishesMotiveIsFalse : sameSuspectLinkEstablishesMotive ≡ false
    sameSuspectLinkIsRelevantCompetingEvidence : Bool
    sameSuspectLinkIsRelevantCompetingEvidenceIsTrue : sameSuspectLinkIsRelevantCompetingEvidence ≡ true
    scientificImportanceOverridesEventSpecificEvidence : Bool
    scientificImportanceOverridesEventSpecificEvidenceIsFalse : scientificImportanceOverridesEventSpecificEvidence ≡ false

canonicalLoureiroEventAlternativeBoundary : LoureiroEventAlternativeBoundary
canonicalLoureiroEventAlternativeBoundary = loureiro-event-alternative-boundary false refl true refl false refl
