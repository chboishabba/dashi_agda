module DASHI.Cognition.PNF.WorkloadGranularityReference where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Workload granularity.
--
-- A note, article, chat and book have radically different coarse document
-- sizes.  Token units are therefore the primary cross-document throughput
-- denominator after tokenisation.  Coarser units remain useful for batching and
-- scheduling, but are not directly comparable without a token count.
------------------------------------------------------------------------

data CoarseContentUnit : Set where
  noteUnit chatTurnUnit articleUnit chapterUnit bookUnit documentUnit :
    CoarseContentUnit

record TokenNormalisedWorkload : Set where
  constructor tokenNormalisedWorkload
  field
    tokenCount : Nat
    coarseUnit : CoarseContentUnit
    coarseUnitCount : Nat
    semanticWorkUnits : Nat
    elapsedUnits : Nat

open TokenNormalisedWorkload public

record ThroughputGranularityBoundary : Set where
  constructor throughputGranularityBoundary
  field
    tokensArePrimaryCrossDocumentScale : Bool
    tokensArePrimaryCrossDocumentScaleIsTrue :
      tokensArePrimaryCrossDocumentScale ≡ true
    documentCountAloneIsComparableAcrossNotesAndBooks : Bool
    documentCountAloneIsComparableAcrossNotesAndBooksIsFalse :
      documentCountAloneIsComparableAcrossNotesAndBooks ≡ false
    coarseUnitsStillUsefulForScheduling : Bool
    coarseUnitsStillUsefulForSchedulingIsTrue :
      coarseUnitsStillUsefulForScheduling ≡ true

open ThroughputGranularityBoundary public

canonicalThroughputGranularityBoundary : ThroughputGranularityBoundary
canonicalThroughputGranularityBoundary =
  throughputGranularityBoundary true refl false refl true refl
