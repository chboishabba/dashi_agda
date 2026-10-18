module DASHI.Law.GenericRecursiveOalcPinnedStreamRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.GenericRecursiveOalcPinnedStreamExact as Stream

boundary : Stream.RecursiveOalcPinnedStreamBoundary
boundary =
  Stream.canonicalRecursiveOalcPinnedStreamBoundary

indexIsOnlyAccelerator :
  Stream.datasetServerIndexIsSourceAuthority boundary ≡ false
indexIsOnlyAccelerator =
  Stream.datasetServerIndexIsSourceAuthorityIsFalse boundary

pinnedRevisionRequired :
  Stream.pinnedCorpusRevisionIsRequired boundary ≡ true
pinnedRevisionRequired =
  Stream.pinnedCorpusRevisionIsRequiredIsTrue boundary

providerFailureFallsBack :
  Stream.indexProviderFailureMayEnterPinnedStream boundary ≡ true
providerFailureFallsBack =
  Stream.indexProviderFailureMayEnterPinnedStreamIsTrue boundary

incompleteIndexFallsBack :
  Stream.incompleteIndexMayEnterPinnedStream boundary ≡ true
incompleteIndexFallsBack =
  Stream.incompleteIndexMayEnterPinnedStreamIsTrue boundary

indexAbsenceMayStillCheckCorpus :
  Stream.completeIndexAbsenceMayEnterPinnedStream boundary ≡ true
indexAbsenceMayStillCheckCorpus =
  Stream.completeIndexAbsenceMayEnterPinnedStreamIsTrue boundary

streamStopsAtExactMnc :
  Stream.pinnedStreamStopsAtFirstExactTerminalMnc boundary ≡ true
streamStopsAtExactMnc =
  Stream.pinnedStreamStopsAtFirstExactTerminalMncIsTrue boundary

firstMatchDoesNotOverclaimUniqueness :
  Stream.firstExactMatchProvesCorpusWideUniqueness boundary ≡ false
firstMatchDoesNotOverclaimUniqueness =
  Stream.firstExactMatchProvesCorpusWideUniquenessIsFalse boundary

scanAccountingPersists :
  Stream.streamRowsAndBytesAreRecorded boundary ≡ true
scanAccountingPersists =
  Stream.streamRowsAndBytesAreRecordedIsTrue boundary

interruptionIsNotAbsence :
  Stream.streamInterruptionCreatesSourceAbsence boundary ≡ false
interruptionIsNotAbsence =
  Stream.streamInterruptionCreatesSourceAbsenceIsFalse boundary

interruptionIsNotLegalEvidence :
  Stream.streamInterruptionCreatesNegativeLegalEvidence boundary ≡ false
interruptionIsNotLegalEvidence =
  Stream.streamInterruptionCreatesNegativeLegalEvidenceIsFalse boundary

streamDoesNotCreateAuthority :
  Stream.successfulPinnedStreamCreatesLegalAuthority boundary ≡ false
streamDoesNotCreateAuthority =
  Stream.successfulPinnedStreamCreatesLegalAuthorityIsFalse boundary

identityReviewStillRequired :
  Stream.identityReviewRemainsRequired boundary ≡ true
identityReviewStillRequired =
  Stream.identityReviewRemainsRequiredIsTrue boundary
