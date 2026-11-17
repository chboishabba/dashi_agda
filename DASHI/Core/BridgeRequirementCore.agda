module DASHI.Core.BridgeRequirementCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Bridge requirement core.
--
-- This module records the reusable fail-closed bridge requirement surface.
-- A supplied bridge can be candidate-only evidence for inspection, but it
-- does not promote authority, transport-map authority, or background-bridge
-- authority.

data BridgeRequirementStatus : Set where
  bridgeRequired :
    BridgeRequirementStatus

  bridgeAbsent :
    BridgeRequirementStatus

  bridgeSuppliedCandidateOnly :
    BridgeRequirementStatus

  backgroundBridgeOnly :
    BridgeRequirementStatus

  transportMapRequired :
    BridgeRequirementStatus

  noBridgePromotion :
    BridgeRequirementStatus

------------------------------------------------------------------------
-- Status-level gates.

statusRequiresBridge :
  BridgeRequirementStatus →
  Bool
statusRequiresBridge bridgeRequired =
  true
statusRequiresBridge bridgeAbsent =
  true
statusRequiresBridge bridgeSuppliedCandidateOnly =
  false
statusRequiresBridge backgroundBridgeOnly =
  false
statusRequiresBridge transportMapRequired =
  true
statusRequiresBridge noBridgePromotion =
  false

statusBridgeSupplied :
  BridgeRequirementStatus →
  Bool
statusBridgeSupplied bridgeRequired =
  false
statusBridgeSupplied bridgeAbsent =
  false
statusBridgeSupplied bridgeSuppliedCandidateOnly =
  true
statusBridgeSupplied backgroundBridgeOnly =
  false
statusBridgeSupplied transportMapRequired =
  false
statusBridgeSupplied noBridgePromotion =
  false

statusCandidateOnly :
  BridgeRequirementStatus →
  Bool
statusCandidateOnly bridgeRequired =
  false
statusCandidateOnly bridgeAbsent =
  false
statusCandidateOnly bridgeSuppliedCandidateOnly =
  true
statusCandidateOnly backgroundBridgeOnly =
  true
statusCandidateOnly transportMapRequired =
  false
statusCandidateOnly noBridgePromotion =
  false

statusAuthorityPromotion :
  BridgeRequirementStatus →
  Bool
statusAuthorityPromotion _ =
  false

statusTransportMapAuthority :
  BridgeRequirementStatus →
  Bool
statusTransportMapAuthority _ =
  false

statusBackgroundBridgeAuthority :
  BridgeRequirementStatus →
  Bool
statusBackgroundBridgeAuthority _ =
  false

statusAuthorityPromotionFalse :
  ∀ status →
  statusAuthorityPromotion status ≡ false
statusAuthorityPromotionFalse status =
  refl

statusTransportMapAuthorityFalse :
  ∀ status →
  statusTransportMapAuthority status ≡ false
statusTransportMapAuthorityFalse status =
  refl

statusBackgroundBridgeAuthorityFalse :
  ∀ status →
  statusBackgroundBridgeAuthority status ≡ false
statusBackgroundBridgeAuthorityFalse status =
  refl

------------------------------------------------------------------------
-- Requirement rows and row receipts.

record BridgeRequirementRow : Set where
  constructor bridgeRequirementRow
  field
    sourceLabel :
      String

    targetLabel :
      String

    requirementStatus :
      BridgeRequirementStatus

    rowBridgeRequired :
      Bool

    rowBridgeSupplied :
      Bool

    rowCandidateOnly :
      Bool

    rowAuthorityPromotion :
      Bool

    rowTransportMapAuthority :
      Bool

    rowBackgroundBridgeAuthority :
      Bool

open BridgeRequirementRow public

record BridgeRequirementRowReceipt
  (row : BridgeRequirementRow) :
  Set where
  constructor bridgeRequirementRowReceipt
  field
    rowAuthorityPromotionFalse :
      rowAuthorityPromotion row ≡ false

    rowTransportMapAuthorityFalse :
      rowTransportMapAuthority row ≡ false

    rowBackgroundBridgeAuthorityFalse :
      rowBackgroundBridgeAuthority row ≡ false

open BridgeRequirementRowReceipt public

canonicalBridgeRequirementRow :
  String →
  String →
  BridgeRequirementStatus →
  Bool →
  Bool →
  Bool →
  BridgeRequirementRow
canonicalBridgeRequirementRow
  source
  target
  status
  required
  supplied
  candidateOnly =
  bridgeRequirementRow
    source
    target
    status
    required
    supplied
    candidateOnly
    false
    false
    false

canonicalBridgeRequirementRowReceipt :
  (row : BridgeRequirementRow) →
  rowAuthorityPromotion row ≡ false →
  rowTransportMapAuthority row ≡ false →
  rowBackgroundBridgeAuthority row ≡ false →
  BridgeRequirementRowReceipt row
canonicalBridgeRequirementRowReceipt row authorityFalse transportFalse backgroundFalse =
  bridgeRequirementRowReceipt
    authorityFalse
    transportFalse
    backgroundFalse

------------------------------------------------------------------------
-- Canonical rows.

suppliedCandidateOnlyBridgeRow :
  BridgeRequirementRow
suppliedCandidateOnlyBridgeRow =
  canonicalBridgeRequirementRow
    "source"
    "target"
    bridgeSuppliedCandidateOnly
    true
    true
    true

absentRequiredBridgeRow :
  BridgeRequirementRow
absentRequiredBridgeRow =
  canonicalBridgeRequirementRow
    "source"
    "target"
    bridgeAbsent
    true
    false
    false

suppliedCandidateOnlyBridgeRowReceipt :
  BridgeRequirementRowReceipt suppliedCandidateOnlyBridgeRow
suppliedCandidateOnlyBridgeRowReceipt =
  bridgeRequirementRowReceipt refl refl refl

absentRequiredBridgeRowReceipt :
  BridgeRequirementRowReceipt absentRequiredBridgeRow
absentRequiredBridgeRowReceipt =
  bridgeRequirementRowReceipt refl refl refl

canonicalBridgeRequirementRows :
  List BridgeRequirementRow
canonicalBridgeRequirementRows =
  suppliedCandidateOnlyBridgeRow
  ∷ absentRequiredBridgeRow
  ∷ []

------------------------------------------------------------------------
-- Projection lemmas for canonical rows.

suppliedCandidateOnlyStatus :
  requirementStatus suppliedCandidateOnlyBridgeRow
  ≡
  bridgeSuppliedCandidateOnly
suppliedCandidateOnlyStatus =
  refl

suppliedCandidateOnlyRequired :
  rowBridgeRequired suppliedCandidateOnlyBridgeRow ≡ true
suppliedCandidateOnlyRequired =
  refl

suppliedCandidateOnlySupplied :
  rowBridgeSupplied suppliedCandidateOnlyBridgeRow ≡ true
suppliedCandidateOnlySupplied =
  refl

suppliedCandidateOnlyCandidateOnly :
  rowCandidateOnly suppliedCandidateOnlyBridgeRow ≡ true
suppliedCandidateOnlyCandidateOnly =
  refl

suppliedCandidateOnlyAuthorityPromotionFalse :
  rowAuthorityPromotion suppliedCandidateOnlyBridgeRow ≡ false
suppliedCandidateOnlyAuthorityPromotionFalse =
  refl

suppliedCandidateOnlyTransportMapAuthorityFalse :
  rowTransportMapAuthority suppliedCandidateOnlyBridgeRow ≡ false
suppliedCandidateOnlyTransportMapAuthorityFalse =
  refl

suppliedCandidateOnlyBackgroundBridgeAuthorityFalse :
  rowBackgroundBridgeAuthority suppliedCandidateOnlyBridgeRow ≡ false
suppliedCandidateOnlyBackgroundBridgeAuthorityFalse =
  refl

absentRequiredStatus :
  requirementStatus absentRequiredBridgeRow ≡ bridgeAbsent
absentRequiredStatus =
  refl

absentRequiredRequired :
  rowBridgeRequired absentRequiredBridgeRow ≡ true
absentRequiredRequired =
  refl

absentRequiredSuppliedFalse :
  rowBridgeSupplied absentRequiredBridgeRow ≡ false
absentRequiredSuppliedFalse =
  refl

absentRequiredCandidateOnlyFalse :
  rowCandidateOnly absentRequiredBridgeRow ≡ false
absentRequiredCandidateOnlyFalse =
  refl

absentRequiredAuthorityPromotionFalse :
  rowAuthorityPromotion absentRequiredBridgeRow ≡ false
absentRequiredAuthorityPromotionFalse =
  refl

absentRequiredTransportMapAuthorityFalse :
  rowTransportMapAuthority absentRequiredBridgeRow ≡ false
absentRequiredTransportMapAuthorityFalse =
  refl

absentRequiredBackgroundBridgeAuthorityFalse :
  rowBackgroundBridgeAuthority absentRequiredBridgeRow ≡ false
absentRequiredBackgroundBridgeAuthorityFalse =
  refl

------------------------------------------------------------------------
-- Core receipt and generic receipt adapter.

record BridgeRequirementCoreReceipt : Set where
  constructor bridgeRequirementCoreReceipt
  field
    receiptRows :
      List BridgeRequirementRow

    receiptRowsAreCanonical :
      receiptRows ≡ canonicalBridgeRequirementRows

    suppliedCandidateOnlyReceipt :
      BridgeRequirementRowReceipt suppliedCandidateOnlyBridgeRow

    absentRequiredReceipt :
      BridgeRequirementRowReceipt absentRequiredBridgeRow

    receiptAuthorityPromotion :
      Bool

    receiptAuthorityPromotionFalse :
      receiptAuthorityPromotion ≡ false

    receiptTransportMapAuthority :
      Bool

    receiptTransportMapAuthorityFalse :
      receiptTransportMapAuthority ≡ false

    receiptBackgroundBridgeAuthority :
      Bool

    receiptBackgroundBridgeAuthorityFalse :
      receiptBackgroundBridgeAuthority ≡ false

open BridgeRequirementCoreReceipt public

canonicalBridgeRequirementCoreReceipt :
  BridgeRequirementCoreReceipt
canonicalBridgeRequirementCoreReceipt =
  bridgeRequirementCoreReceipt
    canonicalBridgeRequirementRows
    refl
    suppliedCandidateOnlyBridgeRowReceipt
    absentRequiredBridgeRowReceipt
    false
    refl
    false
    refl
    false
    refl

bridgeRequirementRowGenericReceipt :
  BridgeRequirementRow →
  GenericReceipt.GenericReceipt
bridgeRequirementRowGenericReceipt row =
  GenericReceipt.mkNonPromotingReceipt
    "bridge requirement row"
    "DASHI.Core.BridgeRequirementCore"
    (sourceLabel row)
    "bridge requirement row records required, supplied, candidate-only, and fail-closed authority gates"
    "bridge requirement rows do not promote authority, transport-map authority, or background-bridge authority"
    "agda -i . DASHI/Core/BridgeRequirementCore.agda"

canonicalBridgeRequirementGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalBridgeRequirementGenericReceipts =
  bridgeRequirementRowGenericReceipt suppliedCandidateOnlyBridgeRow
  ∷ bridgeRequirementRowGenericReceipt absentRequiredBridgeRow
  ∷ []

canonicalBridgeRequirementGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalBridgeRequirementGenericReceipts
canonicalBridgeRequirementGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalBridgeRequirementGenericReceipts
