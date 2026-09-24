module DASHI.Law.GenericRecursiveOalcRangeIndexRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.GenericRecursiveOalcRangeIndexExact as Range

boundary : Range.RecursiveOalcRangeIndexBoundary
boundary =
  Range.canonicalRecursiveOalcRangeIndexBoundary

revisionPinned :
  Range.indexIsKeyedByImmutableRevision boundary ≡ true
revisionPinned =
  Range.indexIsKeyedByImmutableRevisionIsTrue boundary

coordinateKeyIsTyped :
  Range.lookupKeyIncludesTerminalMncTypeAndJurisdiction boundary ≡ true
coordinateKeyIsTyped =
  Range.lookupKeyIncludesTerminalMncTypeAndJurisdictionIsTrue boundary

indexDoesNotStoreCorpus :
  Range.indexStoresCorpusText boundary ≡ false
indexDoesNotStoreCorpus =
  Range.indexStoresCorpusTextIsFalse boundary

rangeAndDigestPersist :
  Range.indexStoresByteRangeAndDigest boundary ≡ true
rangeAndDigestPersist =
  Range.indexStoresByteRangeAndDigestIsTrue boundary

rangeParsingIsRowBounded :
  Range.rangeChunksAreParsedRowByRow boundary ≡ true
rangeParsingIsRowBounded =
  Range.rangeChunksAreParsedRowByRowIsTrue boundary

checkpointStopsAtCompleteRow :
  Range.checkpointAdvancesPastPartialRow boundary ≡ false
checkpointStopsAtCompleteRow =
  Range.checkpointAdvancesPastPartialRowIsFalse boundary

partialRowIsRefetched :
  Range.partialTrailingRowIsRefetched boundary ≡ true
partialRowIsRefetched =
  Range.partialTrailingRowIsRefetchedIsTrue boundary

buildIsResumable :
  Range.interruptedBuildIsResumable boundary ≡ true
buildIsResumable =
  Range.interruptedBuildIsResumableIsTrue boundary

indexHitFetchesExactRange :
  Range.indexHitFetchesExactRecordedRange boundary ≡ true
indexHitFetchesExactRange =
  Range.indexHitFetchesExactRecordedRangeIsTrue boundary

digestIsRevalidated :
  Range.fetchedRangeDigestIsRevalidated boundary ≡ true
digestIsRevalidated =
  Range.fetchedRangeDigestIsRevalidatedIsTrue boundary

rowStillMustMatchDemand :
  Range.fetchedRowMustStillMatchExactDemand boundary ≡ true
rowStillMustMatchDemand =
  Range.fetchedRowMustStillMatchExactDemandIsTrue boundary

partialMissIsNotAbsence :
  Range.missingEntryInPartialIndexMeansSourceAbsent boundary ≡ false
partialMissIsNotAbsence =
  Range.missingEntryInPartialIndexMeansSourceAbsentIsFalse boundary

completeMissIsNotNegativeEvidence :
  Range.completedIndexAbsenceCreatesNegativeLegalEvidence boundary ≡ false
completeMissIsNotNegativeEvidence =
  Range.completedIndexAbsenceCreatesNegativeLegalEvidenceIsFalse boundary

indexCreatesNoAuthority :
  Range.rangeIndexCreatesLegalAuthority boundary ≡ false
indexCreatesNoAuthority =
  Range.rangeIndexCreatesLegalAuthorityIsFalse boundary

indexCreatesNoTruth :
  Range.rangeIndexCreatesClaimTruth boundary ≡ false
indexCreatesNoTruth =
  Range.rangeIndexCreatesClaimTruthIsFalse boundary

identityReviewStillRequired :
  Range.identityReviewRemainsRequired boundary ≡ true
identityReviewStillRequired =
  Range.identityReviewRemainsRequiredIsTrue boundary
