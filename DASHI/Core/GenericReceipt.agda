module DASHI.Core.GenericReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Generic repo-wide receipt metadata.
--
-- This core is intentionally independent of promotion, physics, authority,
-- and obligation-index modules.  It records the common metadata shape used
-- by receipt summaries and keeps the default promotion claim fail-closed.

receiptCount : ∀ {A : Set} → List A → Nat
receiptCount [] =
  zero
receiptCount (_ ∷ receipts) =
  suc (receiptCount receipts)

------------------------------------------------------------------------
-- Receipt vocabulary.

data ReceiptPromotionStatus : Set where
  receiptNonPromoting :
    ReceiptPromotionStatus

  receiptPromotionClaimed :
    ReceiptPromotionStatus

data ReceiptPolarity : Set where
  failClosedReceipt :
    ReceiptPolarity

  advancingReceipt :
    ReceiptPolarity

  blockingReceipt :
    ReceiptPolarity

  boundaryReceipt :
    ReceiptPolarity

------------------------------------------------------------------------
-- Generic receipt record.

record GenericReceipt : Set where
  constructor mkGenericReceipt
  field
    receiptLabel :
      String

    receiptOwner :
      String

    receiptSurface :
      String

    receiptAdvance :
      String

    receiptRemainingGap :
      String

    validationCommand :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open GenericReceipt public

mkNonPromotingReceipt :
  String →
  String →
  String →
  String →
  String →
  String →
  GenericReceipt
mkNonPromotingReceipt label owner surface advance remainingGap command =
  mkGenericReceipt
    label
    owner
    surface
    advance
    remainingGap
    command
    false
    refl

receiptPromotionStatus :
  GenericReceipt →
  ReceiptPromotionStatus
receiptPromotionStatus receipt =
  receiptNonPromoting

receiptDefaultPolarity :
  GenericReceipt →
  ReceiptPolarity
receiptDefaultPolarity receipt =
  failClosedReceipt

receiptIsNonPromoting :
  (receipt : GenericReceipt) →
  promotesClaim receipt ≡ false
receiptIsNonPromoting receipt =
  promotesClaimIsFalse receipt

------------------------------------------------------------------------
-- List-level non-promotion proof.

data AllReceiptsNonPromoting : List GenericReceipt → Set where
  allReceiptsNonPromotingNil :
    AllReceiptsNonPromoting []

  allReceiptsNonPromotingCons :
    ∀ {receipt receipts} →
    promotesClaim receipt ≡ false →
    AllReceiptsNonPromoting receipts →
    AllReceiptsNonPromoting (receipt ∷ receipts)

proveAllReceiptsNonPromoting :
  (receipts : List GenericReceipt) →
  AllReceiptsNonPromoting receipts
proveAllReceiptsNonPromoting [] =
  allReceiptsNonPromotingNil
proveAllReceiptsNonPromoting (receipt ∷ receipts) =
  allReceiptsNonPromotingCons
    (promotesClaimIsFalse receipt)
    (proveAllReceiptsNonPromoting receipts)

------------------------------------------------------------------------
-- Canonical core receipts.

canonicalGenericReceiptCoreReceipt :
  GenericReceipt
canonicalGenericReceiptCoreReceipt =
  mkNonPromotingReceipt
    "generic receipt core"
    "DASHI.Core.GenericReceipt"
    "canonicalGenericReceiptCoreReceipt"
    "repo-wide receipt metadata, fail-closed promotion bit, list proof, and count helper are centralized"
    "downstream modules must still map their domain-specific receipt payloads into this generic surface"
    "agda -i . DASHI/Core/GenericReceipt.agda"

canonicalGenericReceiptSummaryBridge :
  GenericReceipt
canonicalGenericReceiptSummaryBridge =
  mkNonPromotingReceipt
    "receipt summary bridge"
    "DASHI.Promotion.ReceiptSummaryCore"
    "canonicalExampleReceipts"
    "promotion receipt summaries have a compatible non-promoting metadata shape"
    "the promotion summary module has not been rewritten to import this core"
    "agda -i . DASHI/Promotion/ReceiptSummaryCore.agda"

canonicalAuthorityGateReceiptBridge :
  GenericReceipt
canonicalAuthorityGateReceiptBridge =
  mkNonPromotingReceipt
    "authority gate receipt bridge"
    "DASHI.Promotion.AuthorityGateCore"
    "canonicalAuthorityGateReceipts"
    "authority-gate receipts already expose local false promotion-gate evidence"
    "authority-kind-specific gate payloads remain outside the generic receipt surface"
    "agda -i . DASHI/Promotion/AuthorityGateCore.agda"

canonicalGenericReceiptExamples :
  List GenericReceipt
canonicalGenericReceiptExamples =
  canonicalGenericReceiptCoreReceipt
  ∷ canonicalGenericReceiptSummaryBridge
  ∷ canonicalAuthorityGateReceiptBridge
  ∷ []

canonicalGenericReceiptExampleCount :
  Nat
canonicalGenericReceiptExampleCount =
  receiptCount canonicalGenericReceiptExamples

canonicalGenericReceiptExamplesNonPromoting :
  AllReceiptsNonPromoting canonicalGenericReceiptExamples
canonicalGenericReceiptExamplesNonPromoting =
  proveAllReceiptsNonPromoting canonicalGenericReceiptExamples
