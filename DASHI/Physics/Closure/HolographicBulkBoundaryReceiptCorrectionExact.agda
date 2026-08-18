module DASHI.Physics.Closure.HolographicBulkBoundaryReceiptCorrectionExact where

------------------------------------------------------------------------
-- CORRECTION / QUARANTINE FOR THE LEGACY HOLOGRAPHIC RECEIPT FLAG
--
-- The legacy HolographicBulkBoundaryReceipt has a field named
-- `continuumYangMillsConstructedIsFalse`, but that field is typed as
-- `continuumYangMillsConstructed ≡ true` and its canonical receipt sets the
-- flag to true.  This contradicts the module-level boundary text saying that
-- no continuum Euclidean Yang--Mills construction is promoted.
--
-- We do not silently reinterpret the legacy proof.  This module exposes the
-- mismatch and supplies a corrected fail-closed boundary for downstream use.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.HolographicBulkBoundaryReceipt as Legacy

legacyCanonicalContinuumFlagIsTrue :
  Legacy.continuumYangMillsConstructed
    Legacy.canonicalHolographicBulkBoundaryReceipt ≡ true
legacyCanonicalContinuumFlagIsTrue =
  Legacy.continuumYangMillsConstructedIsFalse
    Legacy.canonicalHolographicBulkBoundaryReceipt

record CorrectedHolographicPromotionBoundary : Set where
  constructor correctedHolographicPromotionBoundary
  field
    dictionaryRecorded : Bool
    dictionaryRecordedIsTrue : dictionaryRecorded ≡ true
    wilsonBoundaryMapCandidateOnly : Bool
    wilsonBoundaryMapCandidateOnlyIsTrue : wilsonBoundaryMapCandidateOnly ≡ true
    continuumYangMillsConstructed : Bool
    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false
    clayYangMillsPromoted : Bool
    clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
    boundaryObservationImpliesBulkReconstruction : Bool
    boundaryObservationImpliesBulkReconstructionIsFalse :
      boundaryObservationImpliesBulkReconstruction ≡ false

canonicalCorrectedHolographicPromotionBoundary :
  CorrectedHolographicPromotionBoundary
canonicalCorrectedHolographicPromotionBoundary =
  correctedHolographicPromotionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl

record LegacyReceiptMismatch : Set where
  constructor legacyReceiptMismatch
  field
    legacyFieldNameClaimsFalse : Bool
    legacyFieldNameClaimsFalseIsTrue : legacyFieldNameClaimsFalse ≡ true
    legacyCanonicalProofActuallyProvesTrue : Bool
    legacyCanonicalProofActuallyProvesTrueIsTrue :
      legacyCanonicalProofActuallyProvesTrue ≡ true
    correctedConsumersMustNotTreatLegacyFlagAsContinuumAuthority : Bool
    correctedConsumersMustNotTreatLegacyFlagAsContinuumAuthorityIsTrue :
      correctedConsumersMustNotTreatLegacyFlagAsContinuumAuthority ≡ true

canonicalLegacyReceiptMismatch : LegacyReceiptMismatch
canonicalLegacyReceiptMismatch =
  legacyReceiptMismatch true refl true refl true refl
