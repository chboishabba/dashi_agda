module DASHI.Promotion.ReceiptSummaryCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Generic non-promoting receipt summary rows.
--
-- This module is intentionally independent of ObligationIndex.  It provides
-- the common row shape used by obligation-index summaries without importing
-- the lane datatypes that consume it.

record ReceiptSummary : Set where
  field
    laneLabel :
      String

    owner :
      String

    surface :
      String

    advance :
      String

    gap :
      String

    validationCommand :
      String

    promotes :
      Bool

    promotesIsFalse :
      promotes ≡ false

open ReceiptSummary public

mkReceiptSummary :
  String →
  String →
  String →
  String →
  String →
  String →
  ReceiptSummary
mkReceiptSummary lane ownerModule canonicalSurface recordedAdvance
  remainingGap command =
  record
    { laneLabel = lane
    ; owner = ownerModule
    ; surface = canonicalSurface
    ; advance = recordedAdvance
    ; gap = remainingGap
    ; validationCommand = command
    ; promotes = false
    ; promotesIsFalse = refl
    }

receiptSummaryGenericReceipt :
  ReceiptSummary →
  GenericReceipt.GenericReceipt
receiptSummaryGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    (laneLabel receipt)
    (owner receipt)
    (surface receipt)
    (advance receipt)
    (gap receipt)
    (validationCommand receipt)

canonicalPromotionLaneReceipt : ReceiptSummary
canonicalPromotionLaneReceipt =
  mkReceiptSummary
    "promotion implementation lane"
    "DASHI.Promotion.StandardModelTerminalObligations"
    "canonicalStandardModelTerminalPromotionObligationReceipt"
    "Standard Model and terminal claim-audit obligations are indexed"
    "Standard Model and terminal/full unification promotion remain false"
    "agda -i . DASHI/Promotion/StandardModelTerminalObligations.agda"

canonicalAdapterAdvancementReceipt : ReceiptSummary
canonicalAdapterAdvancementReceipt =
  mkReceiptSummary
    "adapter advancement lane"
    "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    "canonicalEmpiricalRuntimeValidationReport"
    "provider payload, observable, projection digest, comparison, covariance, holdout, replay, and semantic-review machinery are recorded"
    "provider authority, comparison law, covariance authority, holdout acceptance, replay authority, and semantic adequacy remain missing"
    "agda -i . DASHI/Promotion/EmpiricalRuntimeReplayAdapter.agda"

canonicalAuthorityBoundaryReceipt : ReceiptSummary
canonicalAuthorityBoundaryReceipt =
  mkReceiptSummary
    "external authority boundary lane"
    "DASHI.Promotion.NumericAuthorityPayloadValidator"
    "canonicalNumericAuthorityPayloadValidatorReceipt"
    "payload schema, source-family coverage, payload envelopes, and loaded-payload counts are normalized"
    "external authority artifact bytes, checksum, raw value text, uncertainty, covariance, consumer ingestion, loaded values, and numeric promotion remain false"
    "agda -i . DASHI/Promotion/NumericAuthorityPayloadValidator.agda"

canonicalExampleReceipts : List ReceiptSummary
canonicalExampleReceipts =
  canonicalPromotionLaneReceipt
  ∷ canonicalAdapterAdvancementReceipt
  ∷ canonicalAuthorityBoundaryReceipt
  ∷ []

canonicalExampleGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalExampleGenericReceipts =
  receiptSummaryGenericReceipt canonicalPromotionLaneReceipt
  ∷ receiptSummaryGenericReceipt canonicalAdapterAdvancementReceipt
  ∷ receiptSummaryGenericReceipt canonicalAuthorityBoundaryReceipt
  ∷ []

canonicalExampleGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting canonicalExampleGenericReceipts
canonicalExampleGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting canonicalExampleGenericReceipts
