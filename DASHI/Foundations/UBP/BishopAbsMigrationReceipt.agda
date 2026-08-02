module DASHI.Foundations.UBP.BishopAbsMigrationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExactRealSourceAtlas as Sources

------------------------------------------------------------------------
-- Focused Agda 2.9 Bishop migration receipt.
--
-- The previous decision tree had two branches:
--
--   A. prove representation-level absolute-value idempotence strongly enough
--      to align K and the multiplication sampling indices;
--   B. replace the original proof with common-index regularity transport.
--
-- Bishop commit d732b0340d729b264227a70fcf38383d8fb3ac3c closes branch A.
-- RealProperties.agda now contains K-abs, K-abs-index and
-- seq-abs-mul-index, and the original absolute-product theorem proceeds by
-- rewriting to the shared multiplication index.  Common-index transport is
-- retained only as a future fallback for genuinely different modulus choices.
------------------------------------------------------------------------

record BishopAbsMigrationStatus : Set where
  constructor bishopAbsMigrationStatus
  field
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String
    sourceRepository : String
    bishopCommit : String
    dashiPinCommit : String

    actualRationalCarrierInspected : Bool
    actualRationalCarrierInspectedIsTrue :
      actualRationalCarrierInspected ≡ true

    unnormalisedAbsIdempotenceUsed : Bool
    unnormalisedAbsIdempotenceUsedIsTrue :
      unnormalisedAbsIdempotenceUsed ≡ true

    kAbsProved : Bool
    kAbsProvedIsTrue : kAbsProved ≡ true

    multiplicationIndexAligned : Bool
    multiplicationIndexAlignedIsTrue :
      multiplicationIndexAligned ≡ true

    seqAbsMulIndexProved : Bool
    seqAbsMulIndexProvedIsTrue :
      seqAbsMulIndexProved ≡ true

    commonIndexTransportRequiredHere : Bool
    commonIndexTransportRequiredHereIsFalse :
      commonIndexTransportRequiredHere ≡ false

    realPropertiesValidated : Bool
    realPropertiesValidatedIsTrue :
      realPropertiesValidated ≡ true

    inverseValidated : Bool
    inverseValidatedIsTrue : inverseValidated ≡ true

    sequenceValidated : Bool
    sequenceValidatedIsTrue : sequenceValidated ≡ true

    validationReading : String

open BishopAbsMigrationStatus public

canonicalBishopAbsMigrationStatus : BishopAbsMigrationStatus
canonicalBishopAbsMigrationStatus =
  bishopAbsMigrationStatus
    (Sources.author Sources.murrayBishopReals)
    (Sources.title Sources.murrayBishopReals)
    "10.48550/arXiv.2205.08354"
    (Sources.canonicalURL Sources.csimmaBishopRepository)
    "d732b0340d729b264227a70fcf38383d8fb3ac3c"
    "7b31431846ede85473454bf4cc57f5fa5d050a95"
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    "RealProperties.agda, Inverse.agda and Sequence.agda passed under the completed Bishop Agda 2.9 migration; git diff --check also passed. The absolute-product seam is closed by representation-level K/index alignment, not by a new common-index analytic proof."

bishopAbsMigrationReceipt : GenericReceipt.GenericReceipt
bishopAbsMigrationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Bishop Agda 2.9 absolute-product migration"
    "DASHI.Foundations.UBP.BishopAbsMigrationReceipt"
    "canonicalBishopAbsMigrationStatus"
    "the pinned Bishop commit proves K-abs, K-abs-index and seq-abs-mul-index and validates RealProperties, Inverse and Sequence under Agda 2.9"
    "this compatibility result does not assert that Bishop regular sequences are the universally optimal executable exact-real backend; common-index transport remains a conditional future technique rather than a requirement for this theorem"
    "vendor/bishop: RealProperties.agda Inverse.agda Sequence.agda"

bishopAbsMigrationReceiptNonPromoting :
  GenericReceipt.promotesClaim bishopAbsMigrationReceipt ≡ false
bishopAbsMigrationReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse bishopAbsMigrationReceipt
