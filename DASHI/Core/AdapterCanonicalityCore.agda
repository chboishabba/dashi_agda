module DASHI.Core.AdapterCanonicalityCore where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable adapter canonicality core.
--
-- This module centralizes the repeated adapter receipt shape: an adapter
-- value is fixed to its canonical representative, and that canonicalization
-- does not promote authority.

data AdapterCanonicalityKind : Set where
  genericAdapterKind :
    AdapterCanonicalityKind

  receiptAdapterKind :
    AdapterCanonicalityKind

  authorityAdapterKind :
    AdapterCanonicalityKind

  bridgeAdapterKind :
    AdapterCanonicalityKind

  namedAdapterKind :
    String →
    AdapterCanonicalityKind

canonicalAdapterCanonicalityKinds :
  List AdapterCanonicalityKind
canonicalAdapterCanonicalityKinds =
  genericAdapterKind
  ∷ receiptAdapterKind
  ∷ authorityAdapterKind
  ∷ bridgeAdapterKind
  ∷ []

------------------------------------------------------------------------
-- Concrete canonical adapter surface.

data AdapterSurface : Set where
  genericAdapter :
    AdapterSurface

  receiptAdapter :
    AdapterSurface

  authorityAdapter :
    AdapterSurface

  bridgeAdapter :
    AdapterSurface

  namedAdapter :
    String →
    AdapterSurface

canonicalAdapter :
  AdapterSurface
canonicalAdapter =
  genericAdapter

------------------------------------------------------------------------
-- Generic adapter canonicality receipt.

record AdapterCanonicalityReceipt
  (A : Set)
  (canonical : A) :
  Set where
  constructor adapterCanonicalityReceipt
  field
    adapterLabel :
      String

    adapterOwner :
      String

    adapterSurface :
      String

    adapterKind :
      AdapterCanonicalityKind

    adapter :
      A

    adapterIsCanonical :
      adapter ≡ canonical

    adapterPromotesAuthority :
      Bool

    adapterPromotesAuthorityIsFalse :
      adapterPromotesAuthority ≡ false

open AdapterCanonicalityReceipt public

mkCanonicalAdapterReceipt :
  {A : Set} →
  String →
  String →
  String →
  AdapterCanonicalityKind →
  (canonical : A) →
  AdapterCanonicalityReceipt A canonical
mkCanonicalAdapterReceipt label owner surface kind canonical =
  adapterCanonicalityReceipt
    label
    owner
    surface
    kind
    canonical
    refl
    false
    refl

------------------------------------------------------------------------
-- Projection lemmas.

adapterCanonical :
  {A : Set} →
  {canonical : A} →
  (receipt : AdapterCanonicalityReceipt A canonical) →
  adapter receipt ≡ canonical
adapterCanonical receipt =
  adapterIsCanonical receipt

adapterAuthorityPromotionFalse :
  {A : Set} →
  {canonical : A} →
  (receipt : AdapterCanonicalityReceipt A canonical) →
  adapterPromotesAuthority receipt ≡ false
adapterAuthorityPromotionFalse receipt =
  adapterPromotesAuthorityIsFalse receipt

------------------------------------------------------------------------
-- Canonical concrete receipt.

canonicalAdapterCanonicalityReceipt :
  AdapterCanonicalityReceipt AdapterSurface canonicalAdapter
canonicalAdapterCanonicalityReceipt =
  mkCanonicalAdapterReceipt
    "adapter canonicality core"
    "DASHI.Core.AdapterCanonicalityCore"
    "canonicalAdapter"
    genericAdapterKind
    canonicalAdapter

canonicalAdapterIsCanonical :
  adapter canonicalAdapterCanonicalityReceipt ≡ canonicalAdapter
canonicalAdapterIsCanonical =
  refl

canonicalAdapterPromotesAuthorityFalse :
  adapterPromotesAuthority canonicalAdapterCanonicalityReceipt ≡ false
canonicalAdapterPromotesAuthorityFalse =
  refl

------------------------------------------------------------------------
-- Generic receipt adapter.

adapterCanonicalityGenericReceipt :
  {A : Set} →
  {canonical : A} →
  AdapterCanonicalityReceipt A canonical →
  GenericReceipt.GenericReceipt
adapterCanonicalityGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    (adapterLabel receipt)
    (adapterOwner receipt)
    (adapterSurface receipt)
    "adapter value is definitionally tied to its canonical representative"
    "domain modules must still supply any authority-bearing acceptance gate separately"
    "agda -i . DASHI/Core/AdapterCanonicalityCore.agda"

canonicalAdapterCanonicalityGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalAdapterCanonicalityGenericReceipt =
  adapterCanonicalityGenericReceipt canonicalAdapterCanonicalityReceipt

canonicalAdapterCanonicalityGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalAdapterCanonicalityGenericReceipt
  ≡
  false
canonicalAdapterCanonicalityGenericReceiptNonPromoting =
  refl

canonicalAdapterCanonicalityGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalAdapterCanonicalityGenericReceipts =
  canonicalAdapterCanonicalityGenericReceipt
  ∷ []

canonicalAdapterCanonicalityGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalAdapterCanonicalityGenericReceipts
canonicalAdapterCanonicalityGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalAdapterCanonicalityGenericReceipts
