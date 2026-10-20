module DASHI.Culture.HistoricalArchiveAbsenceNonfactorabilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- HISTORICAL ARCHIVE ABSENCE NON-INFERENCE
--
-- A documentary projection may omit a historically present event, subject,
-- belief or testimony.  Therefore documentary non-observation cannot recover
-- world absence unless a separate completeness/reflection witness is supplied.
------------------------------------------------------------------------

data HistoricalState : Set where
  presentButUnrecorded : HistoricalState
  absentAndUnrecorded : HistoricalState

data ArchiveObservation : Set where
  notRecorded : ArchiveObservation

data WorldPresence : Set where
  presentInWorld : WorldPresence
  absentInWorld : WorldPresence

archiveObservation : HistoricalState → ArchiveObservation
archiveObservation _ = notRecorded

worldPresence : HistoricalState → WorldPresence
worldPresence presentButUnrecorded = presentInWorld
worldPresence absentAndUnrecorded = absentInWorld

sameArchiveAbsence :
  archiveObservation presentButUnrecorded
  ≡ archiveObservation absentAndUnrecorded
sameArchiveAbsence = refl

worldPresenceDiffers :
  worldPresence presentButUnrecorded
  ≡ worldPresence absentAndUnrecorded → ⊥
worldPresenceDiffers ()

absenceInArchiveCannotRecoverAbsenceInWorld :
  INF.FactorsThrough archiveObservation worldPresence → ⊥
absenceInArchiveCannotRecoverAbsenceInWorld =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      presentButUnrecorded
      absentAndUnrecorded
      sameArchiveAbsence
      worldPresenceDiffers)

------------------------------------------------------------------------
-- Completeness is proof-relevant, not a default property of an archive.
------------------------------------------------------------------------

record ArchiveCompletenessWitness : Set where
  constructor archive-completeness-witness
  field
    absenceReflectsWorldAbsence :
      (state : HistoricalState) →
      archiveObservation state ≡ notRecorded →
      worldPresence state ≡ absentInWorld

open ArchiveCompletenessWitness public

archiveCompletenessRequiresWitness :
  ArchiveCompletenessWitness → ArchiveCompletenessWitness
archiveCompletenessRequiresWitness witness = witness

canonicalArchiveIsNotComplete : ArchiveCompletenessWitness → ⊥
canonicalArchiveIsNotComplete witness with
  absenceReflectsWorldAbsence witness presentButUnrecorded refl
... | ()

record HistoricalArchiveBoundary : Set where
  constructor historical-archive-boundary
  field
    documentarySilenceProvesWorldAbsence : Bool
    documentarySilenceProvesWorldAbsenceIsFalse :
      documentarySilenceProvesWorldAbsence ≡ false
    completenessMayBeAssumedWithoutWitness : Bool
    completenessMayBeAssumedWithoutWitnessIsFalse :
      completenessMayBeAssumedWithoutWitness ≡ false
    finiteWitnessClaimsEveryHistoricalArchiveIsIncomplete : Bool
    finiteWitnessClaimsEveryHistoricalArchiveIsIncompleteIsFalse :
      finiteWitnessClaimsEveryHistoricalArchiveIsIncomplete ≡ false

canonicalHistoricalArchiveBoundary : HistoricalArchiveBoundary
canonicalHistoricalArchiveBoundary =
  historical-archive-boundary false refl false refl false refl
