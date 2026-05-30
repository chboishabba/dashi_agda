module DASHI.Physics.Closure.ZeroMeanSubspaceGramReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFrameRestrictionReceipt as Restrict

data ZeroMeanGramFact : Set where
  haarWaveletsAlreadyZeroMean :
    ZeroMeanGramFact

  sameBaseBlocksRemainIdentity :
    ZeroMeanGramFact

  crossBaseEntriesUnchanged :
    ZeroMeanGramFact

  constantFunctionIssueWasCompletenessIssue :
    ZeroMeanGramFact

canonicalZeroMeanGramFacts : List ZeroMeanGramFact
canonicalZeroMeanGramFacts =
  haarWaveletsAlreadyZeroMean
  ∷ sameBaseBlocksRemainIdentity
  ∷ crossBaseEntriesUnchanged
  ∷ constantFunctionIssueWasCompletenessIssue
  ∷ []

zeroMeanGramStatement : String
zeroMeanGramStatement =
  "Restricting to L2_0 removes constants but does not change Haar-wavelet Gram entries; the restricted lower bound still depends on off-diagonal operator control."

record ZeroMeanSubspaceGramReceipt : Setω where
  field
    restrictionReceipt :
      Restrict.NSFrameRestrictionReceipt

    restrictedFrameStillOpen :
      Restrict.restrictedFrameBoundProved restrictionReceipt ≡ false

    facts :
      List ZeroMeanGramFact

    factsAreCanonical :
      facts ≡ canonicalZeroMeanGramFacts

    gramMatrixOnL2ZeroSameAsWaveletSubspace :
      Bool

    gramMatrixOnL2ZeroSameAsWaveletSubspaceIsTrue :
      gramMatrixOnL2ZeroSameAsWaveletSubspace ≡ true

    zeroMeanDoesNotChangeGramEntries :
      Bool

    zeroMeanDoesNotChangeGramEntriesIsTrue :
      zeroMeanDoesNotChangeGramEntries ≡ true

    haarWaveletsZeroMeanRecorded :
      Bool

    haarWaveletsZeroMeanRecordedIsTrue :
      haarWaveletsZeroMeanRecorded ≡ true

    constantIssueIsCompletenessNotGramEntry :
      Bool

    constantIssueIsCompletenessNotGramEntryIsTrue :
      constantIssueIsCompletenessNotGramEntry ≡ true

    constantIssueIsWaveletGramEntryIssue :
      Bool

    constantIssueIsWaveletGramEntryIssueIsFalse :
      constantIssueIsWaveletGramEntryIssue ≡ false

    restrictedLowerFrameBoundProved :
      Bool

    restrictedLowerFrameBoundProvedIsFalse :
      restrictedLowerFrameBoundProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ zeroMeanGramStatement

    receiptBoundary :
      List String

open ZeroMeanSubspaceGramReceipt public

canonicalZeroMeanSubspaceGramReceipt :
  ZeroMeanSubspaceGramReceipt
canonicalZeroMeanSubspaceGramReceipt =
  record
    { restrictionReceipt =
        Restrict.canonicalNSFrameRestrictionReceipt
    ; restrictedFrameStillOpen =
        refl
    ; facts =
        canonicalZeroMeanGramFacts
    ; factsAreCanonical =
        refl
    ; gramMatrixOnL2ZeroSameAsWaveletSubspace =
        true
    ; gramMatrixOnL2ZeroSameAsWaveletSubspaceIsTrue =
        refl
    ; zeroMeanDoesNotChangeGramEntries =
        true
    ; zeroMeanDoesNotChangeGramEntriesIsTrue =
        refl
    ; haarWaveletsZeroMeanRecorded =
        true
    ; haarWaveletsZeroMeanRecordedIsTrue =
        refl
    ; constantIssueIsCompletenessNotGramEntry =
        true
    ; constantIssueIsCompletenessNotGramEntryIsTrue =
        refl
    ; constantIssueIsWaveletGramEntryIssue =
        false
    ; constantIssueIsWaveletGramEntryIssueIsFalse =
        refl
    ; restrictedLowerFrameBoundProved =
        false
    ; restrictedLowerFrameBoundProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        zeroMeanGramStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The L2_0 restriction is recorded for the NS frame route"
        ∷ "Haar wavelets are already zero-mean, so restricting to L2_0 leaves Haar-Haar Gram entries unchanged"
        ∷ "The constant issue is a completeness/scaling-function issue, not a wavelet Gram-entry issue"
        ∷ "The restricted frame lower bound and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

zeroMeanSubspaceGramEntriesUnchanged :
  zeroMeanDoesNotChangeGramEntries canonicalZeroMeanSubspaceGramReceipt
  ≡
  true
zeroMeanSubspaceGramEntriesUnchanged =
  refl

zeroMeanSubspaceConstantIssueNotGramEntry :
  constantIssueIsWaveletGramEntryIssue canonicalZeroMeanSubspaceGramReceipt
  ≡
  false
zeroMeanSubspaceConstantIssueNotGramEntry =
  refl

zeroMeanSubspaceGramKeepsClayFalse :
  clayNavierStokesPromoted canonicalZeroMeanSubspaceGramReceipt ≡ false
zeroMeanSubspaceGramKeepsClayFalse =
  refl
