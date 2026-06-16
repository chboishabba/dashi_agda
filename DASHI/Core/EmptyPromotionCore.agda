module DASHI.Core.EmptyPromotionCore where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.FiniteReceiptList as FiniteReceiptList
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable empty promotion core.
--
-- This module centralizes the common fail-closed pattern used by modules
-- whose canonical promotion surface is intentionally empty.

data EmptyPromotionToken : Set where

emptyPromotionImpossible :
  EmptyPromotionToken →
  ⊥
emptyPromotionImpossible ()

canonicalEmptyPromotions :
  List EmptyPromotionToken
canonicalEmptyPromotions =
  []

canonicalEmptyPromotionsAreEmpty :
  canonicalEmptyPromotions ≡ []
canonicalEmptyPromotionsAreEmpty =
  refl

canonicalEmptyPromotionFiniteList :
  FiniteReceiptList.CanonicalFiniteList EmptyPromotionToken
canonicalEmptyPromotionFiniteList =
  FiniteReceiptList.canonicalEmptyList

canonicalEmptyPromotionFiniteListItemsAreEmpty :
  FiniteReceiptList.canonicalItems canonicalEmptyPromotionFiniteList
  ≡
  []
canonicalEmptyPromotionFiniteListItemsAreEmpty =
  refl

canonicalEmptyPromotionFiniteListCountIsZero :
  FiniteReceiptList.canonicalCount canonicalEmptyPromotionFiniteList
  ≡
  zero
canonicalEmptyPromotionFiniteListCountIsZero =
  refl

data EmptyPromotionReceiptComponent : Set where
  emptyPromotionTokenComponent :
    EmptyPromotionReceiptComponent

  emptyPromotionImpossibleComponent :
    EmptyPromotionReceiptComponent

  emptyPromotionListComponent :
    EmptyPromotionReceiptComponent

  emptyPromotionFiniteListComponent :
    EmptyPromotionReceiptComponent

  emptyPromotionGenericReceiptAdapterComponent :
    EmptyPromotionReceiptComponent

canonicalEmptyPromotionReceiptComponents :
  List EmptyPromotionReceiptComponent
canonicalEmptyPromotionReceiptComponents =
  emptyPromotionTokenComponent
  ∷ emptyPromotionImpossibleComponent
  ∷ emptyPromotionListComponent
  ∷ emptyPromotionFiniteListComponent
  ∷ emptyPromotionGenericReceiptAdapterComponent
  ∷ []

record EmptyPromotionReceipt : Set where
  constructor mkEmptyPromotionReceipt
  field
    promotions :
      List EmptyPromotionToken

    promotionsAreEmpty :
      promotions ≡ []

    promotionImpossible :
      EmptyPromotionToken →
      ⊥

    finitePromotionList :
      FiniteReceiptList.CanonicalFiniteList EmptyPromotionToken

    finitePromotionListIsCanonical :
      finitePromotionList ≡ canonicalEmptyPromotionFiniteList

    receiptComponents :
      List EmptyPromotionReceiptComponent

    receiptComponentsAreCanonical :
      receiptComponents ≡ canonicalEmptyPromotionReceiptComponents

open EmptyPromotionReceipt public

canonicalEmptyPromotionReceipt :
  EmptyPromotionReceipt
canonicalEmptyPromotionReceipt =
  mkEmptyPromotionReceipt
    canonicalEmptyPromotions
    canonicalEmptyPromotionsAreEmpty
    emptyPromotionImpossible
    canonicalEmptyPromotionFiniteList
    refl
    canonicalEmptyPromotionReceiptComponents
    refl

emptyPromotionReceiptPromotionsAreEmpty :
  (receipt : EmptyPromotionReceipt) →
  promotions receipt ≡ []
emptyPromotionReceiptPromotionsAreEmpty receipt =
  promotionsAreEmpty receipt

emptyPromotionReceiptPromotionImpossible :
  (receipt : EmptyPromotionReceipt) →
  EmptyPromotionToken →
  ⊥
emptyPromotionReceiptPromotionImpossible receipt =
  promotionImpossible receipt

emptyPromotionReceiptFiniteListIsCanonical :
  (receipt : EmptyPromotionReceipt) →
  finitePromotionList receipt ≡ canonicalEmptyPromotionFiniteList
emptyPromotionReceiptFiniteListIsCanonical receipt =
  finitePromotionListIsCanonical receipt

canonicalEmptyPromotionReceiptPromotionsAreEmpty :
  promotions canonicalEmptyPromotionReceipt ≡ []
canonicalEmptyPromotionReceiptPromotionsAreEmpty =
  refl

canonicalEmptyPromotionReceiptComponentsAreCanonical :
  receiptComponents canonicalEmptyPromotionReceipt
  ≡
  canonicalEmptyPromotionReceiptComponents
canonicalEmptyPromotionReceiptComponentsAreCanonical =
  refl

record EmptyPromotionBundle : Set where
  constructor mkEmptyPromotionBundle
  field
    bundleLabel :
      String

    bundleOwner :
      String

    bundleSurface :
      String

    bundleAdvance :
      String

    bundleRemainingGap :
      String

    bundleValidationCommand :
      String

    emptyPromotionReceipt :
      EmptyPromotionReceipt

    emptyPromotionReceiptIsCanonical :
      emptyPromotionReceipt ≡ canonicalEmptyPromotionReceipt

open EmptyPromotionBundle public

canonicalEmptyPromotionBundle :
  EmptyPromotionBundle
canonicalEmptyPromotionBundle =
  mkEmptyPromotionBundle
    "empty promotion core"
    "DASHI.Core.EmptyPromotionCore"
    "canonicalEmptyPromotionReceipt"
    "centralizes the empty-promotion token, impossible eliminator, empty list proof, finite-list receipt, and generic receipt adapter"
    "downstream modules must still bind their domain-specific receipt payloads to this empty promotion surface"
    "agda -i . DASHI/Core/EmptyPromotionCore.agda"
    canonicalEmptyPromotionReceipt
    refl

canonicalEmptyPromotionBundleReceiptIsCanonical :
  emptyPromotionReceipt canonicalEmptyPromotionBundle
  ≡
  canonicalEmptyPromotionReceipt
canonicalEmptyPromotionBundleReceiptIsCanonical =
  refl

canonicalEmptyPromotionBundlePromotionsAreEmpty :
  promotions (emptyPromotionReceipt canonicalEmptyPromotionBundle)
  ≡
  []
canonicalEmptyPromotionBundlePromotionsAreEmpty =
  refl

canonicalEmptyPromotionBundlePromotionImpossible :
  EmptyPromotionToken →
  ⊥
canonicalEmptyPromotionBundlePromotionImpossible =
  promotionImpossible (emptyPromotionReceipt canonicalEmptyPromotionBundle)

canonicalEmptyPromotionBundleFiniteListIsCanonical :
  finitePromotionList (emptyPromotionReceipt canonicalEmptyPromotionBundle)
  ≡
  canonicalEmptyPromotionFiniteList
canonicalEmptyPromotionBundleFiniteListIsCanonical =
  refl

emptyPromotionGenericReceipt :
  EmptyPromotionBundle →
  GenericReceipt.GenericReceipt
emptyPromotionGenericReceipt bundle =
  GenericReceipt.mkNonPromotingReceipt
    (bundleLabel bundle)
    (bundleOwner bundle)
    (bundleSurface bundle)
    (bundleAdvance bundle)
    (bundleRemainingGap bundle)
    (bundleValidationCommand bundle)

canonicalEmptyPromotionGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalEmptyPromotionGenericReceipt =
  emptyPromotionGenericReceipt canonicalEmptyPromotionBundle

canonicalEmptyPromotionGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalEmptyPromotionGenericReceipt
  ≡
  false
canonicalEmptyPromotionGenericReceiptNonPromoting =
  refl

canonicalEmptyPromotionGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalEmptyPromotionGenericReceipts =
  canonicalEmptyPromotionGenericReceipt
  ∷ []

canonicalEmptyPromotionGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalEmptyPromotionGenericReceipts
canonicalEmptyPromotionGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalEmptyPromotionGenericReceipts
