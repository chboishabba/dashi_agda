module DASHI.Foundations.CarrierPromotionBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable fail-closed carrier-promotion boundary core.

data CarrierKind : Set where
  qq-carrier :
    CarrierKind

  surreal-carrier :
    CarrierKind

  ordered-qq-carrier :
    CarrierKind

  analytic-tail-bound-carrier :
    CarrierKind

data TailBoundStatus : Set where
  analytic-tail-bound-not-proved-here :
    TailBoundStatus

record CarrierPromotionBoundary : Set where
  constructor fail-closed-carrier-promotion-boundary
  field
    carrierKind :
      CarrierKind

    boundaryLabel :
      String

    constructedHere :
      Bool

    constructedHereIsFalse :
      constructedHere ≡ false

    promotedHere :
      Bool

    promotedHereIsFalse :
      promotedHere ≡ false

    qqCarrierPromoted :
      Bool

    qqCarrierPromotedIsFalse :
      qqCarrierPromoted ≡ false

    surrealCarrierPromoted :
      Bool

    surrealCarrierPromotedIsFalse :
      surrealCarrierPromoted ≡ false

    orderedQQCarrierPromoted :
      Bool

    orderedQQCarrierPromotedIsFalse :
      orderedQQCarrierPromoted ≡ false

    analyticTailBoundProvedHere :
      Bool

    analyticTailBoundProvedHereIsFalse :
      analyticTailBoundProvedHere ≡ false

    analyticTailBoundPromoted :
      Bool

    analyticTailBoundPromotedIsFalse :
      analyticTailBoundPromoted ≡ false

    tailBoundStatus :
      TailBoundStatus

    tailBoundStatusIsNotProvedHere :
      tailBoundStatus ≡ analytic-tail-bound-not-proved-here

open CarrierPromotionBoundary public

failClosedLocalCarrierPromotionBoundary :
  CarrierKind →
  String →
  CarrierPromotionBoundary
failClosedLocalCarrierPromotionBoundary kind label =
  fail-closed-carrier-promotion-boundary
    kind
    label
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    analytic-tail-bound-not-proved-here
    refl

record CarrierPromotionReceipt : Set where
  constructor fail-closed-local-carrier-promotion-receipt
  field
    boundary :
      CarrierPromotionBoundary

    receiptConstructedHere :
      Bool

    receiptConstructedHereIsFalse :
      receiptConstructedHere ≡ false

    receiptPromotedHere :
      Bool

    receiptPromotedHereIsFalse :
      receiptPromotedHere ≡ false

    boundaryConstructedHereIsFalse :
      constructedHere boundary ≡ false

    boundaryPromotedHereIsFalse :
      promotedHere boundary ≡ false

    boundaryQQCarrierPromotedIsFalse :
      qqCarrierPromoted boundary ≡ false

    boundaryAnalyticTailBoundProvedHereIsFalse :
      analyticTailBoundProvedHere boundary ≡ false

open CarrierPromotionReceipt public

failClosedLocalCarrierPromotionReceipt :
  CarrierPromotionBoundary →
  CarrierPromotionReceipt
failClosedLocalCarrierPromotionReceipt boundary =
  fail-closed-local-carrier-promotion-receipt
    boundary
    false
    refl
    false
    refl
    (constructedHereIsFalse boundary)
    (promotedHereIsFalse boundary)
    (qqCarrierPromotedIsFalse boundary)
    (analyticTailBoundProvedHereIsFalse boundary)

------------------------------------------------------------------------
-- Canonical reusable receipts.

canonicalQQCarrierPromotionBoundary :
  CarrierPromotionBoundary
canonicalQQCarrierPromotionBoundary =
  failClosedLocalCarrierPromotionBoundary
    qq-carrier
    "QQ carrier not promoted here"

canonicalSurrealCarrierPromotionBoundary :
  CarrierPromotionBoundary
canonicalSurrealCarrierPromotionBoundary =
  failClosedLocalCarrierPromotionBoundary
    surreal-carrier
    "surreal carrier not promoted here"

canonicalOrderedQQCarrierPromotionBoundary :
  CarrierPromotionBoundary
canonicalOrderedQQCarrierPromotionBoundary =
  failClosedLocalCarrierPromotionBoundary
    ordered-qq-carrier
    "ordered QQ carrier not promoted here"

canonicalTailBoundPromotionBoundary :
  CarrierPromotionBoundary
canonicalTailBoundPromotionBoundary =
  failClosedLocalCarrierPromotionBoundary
    analytic-tail-bound-carrier
    "analytic tail bound not proved here"

canonicalQQCarrierPromotionReceipt :
  CarrierPromotionReceipt
canonicalQQCarrierPromotionReceipt =
  failClosedLocalCarrierPromotionReceipt
    canonicalQQCarrierPromotionBoundary

canonicalSurrealCarrierPromotionReceipt :
  CarrierPromotionReceipt
canonicalSurrealCarrierPromotionReceipt =
  failClosedLocalCarrierPromotionReceipt
    canonicalSurrealCarrierPromotionBoundary

canonicalOrderedQQCarrierPromotionReceipt :
  CarrierPromotionReceipt
canonicalOrderedQQCarrierPromotionReceipt =
  failClosedLocalCarrierPromotionReceipt
    canonicalOrderedQQCarrierPromotionBoundary

canonicalTailBoundPromotionReceipt :
  CarrierPromotionReceipt
canonicalTailBoundPromotionReceipt =
  failClosedLocalCarrierPromotionReceipt
    canonicalTailBoundPromotionBoundary

canonicalQQCarrierNotPromoted :
  qqCarrierPromoted
    (boundary canonicalQQCarrierPromotionReceipt)
  ≡
  false
canonicalQQCarrierNotPromoted =
  refl

canonicalSurrealCarrierNotPromoted :
  surrealCarrierPromoted
    (boundary canonicalSurrealCarrierPromotionReceipt)
  ≡
  false
canonicalSurrealCarrierNotPromoted =
  refl

canonicalOrderedQQCarrierNotPromoted :
  orderedQQCarrierPromoted
    (boundary canonicalOrderedQQCarrierPromotionReceipt)
  ≡
  false
canonicalOrderedQQCarrierNotPromoted =
  refl

canonicalTailBoundNotProvedHere :
  analyticTailBoundProvedHere
    (boundary canonicalTailBoundPromotionReceipt)
  ≡
  false
canonicalTailBoundNotProvedHere =
  refl

canonicalTailBoundNotPromoted :
  analyticTailBoundPromoted
    (boundary canonicalTailBoundPromotionReceipt)
  ≡
  false
canonicalTailBoundNotPromoted =
  refl

carrierPromotionGenericReceipt :
  CarrierPromotionReceipt →
  GenericReceipt.GenericReceipt
carrierPromotionGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    (boundaryLabel (boundary receipt))
    "DASHI.Foundations.CarrierPromotionBoundaryCore"
    "canonical carrier promotion boundary receipts"
    "carrier promotion receipt records constructedHere, promotedHere, QQ/surreal/ordered-QQ promotion, and analytic-tail-bound proof bits as false"
    "carrier construction, ordered-QQ promotion, and analytic tail-bound authority remain outside this boundary core"
    "agda -i . DASHI/Foundations/CarrierPromotionBoundaryCore.agda"

canonicalCarrierPromotionGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalCarrierPromotionGenericReceipts =
  carrierPromotionGenericReceipt canonicalQQCarrierPromotionReceipt
  ∷ carrierPromotionGenericReceipt canonicalSurrealCarrierPromotionReceipt
  ∷ carrierPromotionGenericReceipt canonicalOrderedQQCarrierPromotionReceipt
  ∷ carrierPromotionGenericReceipt canonicalTailBoundPromotionReceipt
  ∷ []

canonicalCarrierPromotionGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting canonicalCarrierPromotionGenericReceipts
canonicalCarrierPromotionGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalCarrierPromotionGenericReceipts
