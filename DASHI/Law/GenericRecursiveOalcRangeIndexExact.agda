module DASHI.Law.GenericRecursiveOalcRangeIndexExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S14.5 range-index transport.
--
-- A range index is infrastructure over one immutable OALC corpus revision.
-- It maps an exact terminal MNC and source coordinates to the byte range of
-- one JSONL row.  It is not legal authority, identity, treatment, or truth.
------------------------------------------------------------------------

record OalcRangeIndexKey : Set where
  constructor oalcRangeIndexKey
  field
    corpusRevisionSha : String
    terminalMnc : String
    documentType : String
    jurisdiction : String

open OalcRangeIndexKey public

record OalcRangeIndexEntry : Set where
  constructor oalcRangeIndexEntry
  field
    key : OalcRangeIndexKey
    source : String
    versionId : String
    byteStart : Nat
    byteLength : Nat
    rowDigest : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open OalcRangeIndexEntry public

record OalcRangeIndexCheckpoint : Set where
  constructor oalcRangeIndexCheckpoint
  field
    revisionSha : String
    nextByteOffset : Nat
    rowsIndexed : Nat
    bytesIndexed : Nat
    checkpointEndsOnCompleteJsonlRow : Bool
    checkpointEndsOnCompleteJsonlRowIsTrue :
      checkpointEndsOnCompleteJsonlRow ≡ true
    complete : Bool
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

open OalcRangeIndexCheckpoint public

record RecursiveOalcRangeIndexBoundary : Set where
  constructor recursiveOalcRangeIndexBoundary
  field
    indexIsKeyedByImmutableRevision : Bool
    indexIsKeyedByImmutableRevisionIsTrue :
      indexIsKeyedByImmutableRevision ≡ true

    lookupKeyIncludesTerminalMncTypeAndJurisdiction : Bool
    lookupKeyIncludesTerminalMncTypeAndJurisdictionIsTrue :
      lookupKeyIncludesTerminalMncTypeAndJurisdiction ≡ true

    indexStoresCorpusText : Bool
    indexStoresCorpusTextIsFalse :
      indexStoresCorpusText ≡ false

    indexStoresByteRangeAndDigest : Bool
    indexStoresByteRangeAndDigestIsTrue :
      indexStoresByteRangeAndDigest ≡ true

    rangeChunksAreParsedRowByRow : Bool
    rangeChunksAreParsedRowByRowIsTrue :
      rangeChunksAreParsedRowByRow ≡ true

    checkpointAdvancesPastPartialRow : Bool
    checkpointAdvancesPastPartialRowIsFalse :
      checkpointAdvancesPastPartialRow ≡ false

    partialTrailingRowIsRefetched : Bool
    partialTrailingRowIsRefetchedIsTrue :
      partialTrailingRowIsRefetched ≡ true

    interruptedBuildIsResumable : Bool
    interruptedBuildIsResumableIsTrue :
      interruptedBuildIsResumable ≡ true

    indexHitFetchesExactRecordedRange : Bool
    indexHitFetchesExactRecordedRangeIsTrue :
      indexHitFetchesExactRecordedRange ≡ true

    fetchedRangeDigestIsRevalidated : Bool
    fetchedRangeDigestIsRevalidatedIsTrue :
      fetchedRangeDigestIsRevalidated ≡ true

    fetchedRowMustStillMatchExactDemand : Bool
    fetchedRowMustStillMatchExactDemandIsTrue :
      fetchedRowMustStillMatchExactDemand ≡ true

    missingEntryInPartialIndexMeansSourceAbsent : Bool
    missingEntryInPartialIndexMeansSourceAbsentIsFalse :
      missingEntryInPartialIndexMeansSourceAbsent ≡ false

    completedIndexAbsenceCreatesNegativeLegalEvidence : Bool
    completedIndexAbsenceCreatesNegativeLegalEvidenceIsFalse :
      completedIndexAbsenceCreatesNegativeLegalEvidence ≡ false

    rangeIndexCreatesLegalAuthority : Bool
    rangeIndexCreatesLegalAuthorityIsFalse :
      rangeIndexCreatesLegalAuthority ≡ false

    rangeIndexCreatesClaimTruth : Bool
    rangeIndexCreatesClaimTruthIsFalse :
      rangeIndexCreatesClaimTruth ≡ false

    identityReviewRemainsRequired : Bool
    identityReviewRemainsRequiredIsTrue :
      identityReviewRemainsRequired ≡ true

open RecursiveOalcRangeIndexBoundary public

canonicalRecursiveOalcRangeIndexBoundary :
  RecursiveOalcRangeIndexBoundary
canonicalRecursiveOalcRangeIndexBoundary =
  recursiveOalcRangeIndexBoundary
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl

data RangeIndexAutomaticallyAuthority : Set where
data PartialIndexMissAutomaticallySourceAbsent : Set where
data CompletedIndexMissAutomaticallyNegativeEvidence : Set where
data RangeIndexHitMaySkipDigestValidation : Set where
data RangeIndexHitMaySkipIdentityReview : Set where

rangeIndexDoesNotCreateAuthority :
  RangeIndexAutomaticallyAuthority → ⊥
rangeIndexDoesNotCreateAuthority ()

partialIndexMissDoesNotBecomeSourceAbsence :
  PartialIndexMissAutomaticallySourceAbsent → ⊥
partialIndexMissDoesNotBecomeSourceAbsence ()

completedIndexMissDoesNotBecomeNegativeEvidence :
  CompletedIndexMissAutomaticallyNegativeEvidence → ⊥
completedIndexMissDoesNotBecomeNegativeEvidence ()

rangeIndexHitCannotSkipDigestValidation :
  RangeIndexHitMaySkipDigestValidation → ⊥
rangeIndexHitCannotSkipDigestValidation ()

rangeIndexHitCannotSkipIdentityReview :
  RangeIndexHitMaySkipIdentityReview → ⊥
rangeIndexHitCannotSkipIdentityReview ()
