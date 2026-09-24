module DASHI.Law.GenericRecursiveOalcPinnedStreamExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S14.5 provider transport seam.
--
-- The HF Dataset Server index is an accelerator.  A revision-pinned stream of
-- the underlying OALC corpus remains an admitted governed source route when
-- the derived search index is incomplete or temporarily unavailable.
------------------------------------------------------------------------

data OalcRecursiveAcquisitionMode : Set where
  indexedOnly : OalcRecursiveAcquisitionMode
  indexedThenPinnedStream : OalcRecursiveAcquisitionMode

record PinnedStreamAccounting : Set where
  constructor pinnedStreamAccounting
  field
    rowsExamined : Nat
    bytesRead : Nat
    terminatedAfterExactMatch : Bool
    terminatedAfterExactMatchIsTrue :
      terminatedAfterExactMatch ≡ true
    uniquenessExhaustivelyVerified : Bool
    uniquenessExhaustivelyVerifiedIsFalse :
      uniquenessExhaustivelyVerified ≡ false

open PinnedStreamAccounting public

record RecursiveOalcPinnedStreamBoundary : Set where
  constructor recursiveOalcPinnedStreamBoundary
  field
    recursiveMode : OalcRecursiveAcquisitionMode

    datasetServerIndexIsSourceAuthority : Bool
    datasetServerIndexIsSourceAuthorityIsFalse :
      datasetServerIndexIsSourceAuthority ≡ false

    pinnedCorpusRevisionIsRequired : Bool
    pinnedCorpusRevisionIsRequiredIsTrue :
      pinnedCorpusRevisionIsRequired ≡ true

    indexProviderFailureMayEnterPinnedStream : Bool
    indexProviderFailureMayEnterPinnedStreamIsTrue :
      indexProviderFailureMayEnterPinnedStream ≡ true

    incompleteIndexMayEnterPinnedStream : Bool
    incompleteIndexMayEnterPinnedStreamIsTrue :
      incompleteIndexMayEnterPinnedStream ≡ true

    completeIndexAbsenceMayEnterPinnedStream : Bool
    completeIndexAbsenceMayEnterPinnedStreamIsTrue :
      completeIndexAbsenceMayEnterPinnedStream ≡ true

    pinnedStreamStopsAtFirstExactTerminalMnc : Bool
    pinnedStreamStopsAtFirstExactTerminalMncIsTrue :
      pinnedStreamStopsAtFirstExactTerminalMnc ≡ true

    firstExactMatchProvesCorpusWideUniqueness : Bool
    firstExactMatchProvesCorpusWideUniquenessIsFalse :
      firstExactMatchProvesCorpusWideUniqueness ≡ false

    streamRowsAndBytesAreRecorded : Bool
    streamRowsAndBytesAreRecordedIsTrue :
      streamRowsAndBytesAreRecorded ≡ true

    streamInterruptionCreatesSourceAbsence : Bool
    streamInterruptionCreatesSourceAbsenceIsFalse :
      streamInterruptionCreatesSourceAbsence ≡ false

    streamInterruptionCreatesNegativeLegalEvidence : Bool
    streamInterruptionCreatesNegativeLegalEvidenceIsFalse :
      streamInterruptionCreatesNegativeLegalEvidence ≡ false

    successfulPinnedStreamCreatesLegalAuthority : Bool
    successfulPinnedStreamCreatesLegalAuthorityIsFalse :
      successfulPinnedStreamCreatesLegalAuthority ≡ false

    identityReviewRemainsRequired : Bool
    identityReviewRemainsRequiredIsTrue :
      identityReviewRemainsRequired ≡ true

open RecursiveOalcPinnedStreamBoundary public

canonicalRecursiveOalcPinnedStreamBoundary :
  RecursiveOalcPinnedStreamBoundary
canonicalRecursiveOalcPinnedStreamBoundary =
  recursiveOalcPinnedStreamBoundary
    indexedThenPinnedStream
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl

data DatasetServerIndexAutomaticallySourceAuthority : Set where
data FirstExactMatchAutomaticallyCorpusUnique : Set where
data InterruptedPinnedStreamAutomaticallySourceAbsent : Set where
data InterruptedPinnedStreamAutomaticallyNegativeEvidence : Set where
data PinnedStreamAutomaticallyLegalAuthority : Set where

datasetServerIndexDoesNotBecomeSourceAuthority :
  DatasetServerIndexAutomaticallySourceAuthority → ⊥
datasetServerIndexDoesNotBecomeSourceAuthority ()

firstExactMatchDoesNotProveCorpusWideUniqueness :
  FirstExactMatchAutomaticallyCorpusUnique → ⊥
firstExactMatchDoesNotProveCorpusWideUniqueness ()

interruptedPinnedStreamDoesNotBecomeSourceAbsence :
  InterruptedPinnedStreamAutomaticallySourceAbsent → ⊥
interruptedPinnedStreamDoesNotBecomeSourceAbsence ()

interruptedPinnedStreamDoesNotBecomeNegativeEvidence :
  InterruptedPinnedStreamAutomaticallyNegativeEvidence → ⊥
interruptedPinnedStreamDoesNotBecomeNegativeEvidence ()

pinnedStreamDoesNotCreateLegalAuthority :
  PinnedStreamAutomaticallyLegalAuthority → ⊥
pinnedStreamDoesNotCreateLegalAuthority ()
