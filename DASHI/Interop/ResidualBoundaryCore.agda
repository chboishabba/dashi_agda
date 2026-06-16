module DASHI.Interop.ResidualBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Residual/comparison boundary core.
--
-- This module is reusable vocabulary only.  It factors the recurring boundary
-- statuses used by residual comparison surfaces: same-fibre exact/partial
-- comparison, same-fibre no typed meet or contradiction, and cross-fibre scope
-- exceedance.  The admissibility gates are fail-closed and no boundary receipt
-- promotes truth, support, or external authority.

data BoundaryResidual : Set where
  exact :
    BoundaryResidual

  partial :
    BoundaryResidual

  noTypedMeet :
    BoundaryResidual

  scopeExceeded :
    BoundaryResidual

  contradiction :
    BoundaryResidual

boundaryResidualToFour :
  BoundaryResidual →
  Residual.ResidualLevel
boundaryResidualToFour exact =
  Residual.exact
boundaryResidualToFour partial =
  Residual.partial
boundaryResidualToFour noTypedMeet =
  Residual.noTypedMeet
boundaryResidualToFour scopeExceeded =
  Residual.noTypedMeet
boundaryResidualToFour contradiction =
  Residual.contradiction

boundaryResidualToSix :
  BoundaryResidual →
  Residual.SixResidualLevel
boundaryResidualToSix exact =
  Residual.exact6
boundaryResidualToSix partial =
  Residual.partial6
boundaryResidualToSix noTypedMeet =
  Residual.noTypedMeet6
boundaryResidualToSix scopeExceeded =
  Residual.scopeExceeded6
boundaryResidualToSix contradiction =
  Residual.contradiction6

boundarySeverity :
  BoundaryResidual →
  Nat
boundarySeverity exact =
  0
boundarySeverity partial =
  1
boundarySeverity noTypedMeet =
  3
boundarySeverity scopeExceeded =
  4
boundarySeverity contradiction =
  9

------------------------------------------------------------------------
-- Inspection and comparison boundary vocabulary.

data InspectionLevel : Set where
  currentStructuralInspection :
    InspectionLevel

  deeperParseInspection :
    InspectionLevel

  bridgeAwareInspection :
    InspectionLevel

  externalAuthorityInspection :
    InspectionLevel

data BridgeRequirement : Set where
  bridgeNotRequired :
    BridgeRequirement

  bridgeRequired :
    BridgeRequirement

  bridgeSatisfied :
    BridgeRequirement

data FibreRelation : Set where
  sameFibre :
    FibreRelation

  crossFibre :
    FibreRelation

data BoundaryKind : Set where
  exactBoundary :
    BoundaryKind

  partialBoundary :
    BoundaryKind

  noTypedMeetBoundary :
    BoundaryKind

  contradictionBoundary :
    BoundaryKind

  scopeExceededBoundary :
    BoundaryKind

boundaryKindResidual :
  BoundaryKind →
  BoundaryResidual
boundaryKindResidual exactBoundary =
  exact
boundaryKindResidual partialBoundary =
  partial
boundaryKindResidual noTypedMeetBoundary =
  noTypedMeet
boundaryKindResidual contradictionBoundary =
  contradiction
boundaryKindResidual scopeExceededBoundary =
  scopeExceeded

boundaryKindFibreRelation :
  BoundaryKind →
  FibreRelation
boundaryKindFibreRelation exactBoundary =
  sameFibre
boundaryKindFibreRelation partialBoundary =
  sameFibre
boundaryKindFibreRelation noTypedMeetBoundary =
  sameFibre
boundaryKindFibreRelation contradictionBoundary =
  sameFibre
boundaryKindFibreRelation scopeExceededBoundary =
  crossFibre

boundaryKindBridgeRequirement :
  BoundaryKind →
  BridgeRequirement
boundaryKindBridgeRequirement exactBoundary =
  bridgeNotRequired
boundaryKindBridgeRequirement partialBoundary =
  bridgeNotRequired
boundaryKindBridgeRequirement noTypedMeetBoundary =
  bridgeNotRequired
boundaryKindBridgeRequirement contradictionBoundary =
  bridgeNotRequired
boundaryKindBridgeRequirement scopeExceededBoundary =
  bridgeRequired

------------------------------------------------------------------------
-- Fail-closed gates.

bridgeRequirementSatisfied :
  BridgeRequirement →
  Bool
bridgeRequirementSatisfied bridgeNotRequired =
  true
bridgeRequirementSatisfied bridgeRequired =
  false
bridgeRequirementSatisfied bridgeSatisfied =
  true

residualAdmissible :
  BoundaryResidual →
  Bool
residualAdmissible exact =
  true
residualAdmissible partial =
  true
residualAdmissible noTypedMeet =
  false
residualAdmissible scopeExceeded =
  false
residualAdmissible contradiction =
  false

boundaryPromotesTruth :
  BoundaryResidual →
  Bool
boundaryPromotesTruth _ =
  false

boundaryPromotesSupport :
  BoundaryResidual →
  Bool
boundaryPromotesSupport _ =
  false

boundaryPromotesExternalAuthority :
  BoundaryResidual →
  Bool
boundaryPromotesExternalAuthority _ =
  false

boundaryComparisonAdmissible :
  FibreRelation →
  BridgeRequirement →
  BoundaryResidual →
  Bool
boundaryComparisonAdmissible sameFibre bridgeNotRequired residual =
  residualAdmissible residual
boundaryComparisonAdmissible sameFibre bridgeSatisfied residual =
  residualAdmissible residual
boundaryComparisonAdmissible sameFibre bridgeRequired _ =
  false
boundaryComparisonAdmissible crossFibre bridgeSatisfied exact =
  true
boundaryComparisonAdmissible crossFibre bridgeSatisfied partial =
  true
boundaryComparisonAdmissible crossFibre bridgeSatisfied noTypedMeet =
  false
boundaryComparisonAdmissible crossFibre bridgeSatisfied scopeExceeded =
  false
boundaryComparisonAdmissible crossFibre bridgeSatisfied contradiction =
  false
boundaryComparisonAdmissible crossFibre bridgeNotRequired _ =
  false
boundaryComparisonAdmissible crossFibre bridgeRequired _ =
  false

boundaryKindAdmissible :
  BoundaryKind →
  Bool
boundaryKindAdmissible kind =
  boundaryComparisonAdmissible
    (boundaryKindFibreRelation kind)
    (boundaryKindBridgeRequirement kind)
    (boundaryKindResidual kind)

boundaryTruthGateFalse :
  ∀ residual →
  boundaryPromotesTruth residual ≡ false
boundaryTruthGateFalse residual =
  refl

boundarySupportGateFalse :
  ∀ residual →
  boundaryPromotesSupport residual ≡ false
boundarySupportGateFalse residual =
  refl

boundaryExternalAuthorityGateFalse :
  ∀ residual →
  boundaryPromotesExternalAuthority residual ≡ false
boundaryExternalAuthorityGateFalse residual =
  refl

bridgeRequiredFailsClosed :
  ∀ relation residual →
  boundaryComparisonAdmissible relation bridgeRequired residual ≡ false
bridgeRequiredFailsClosed sameFibre residual =
  refl
bridgeRequiredFailsClosed crossFibre residual =
  refl

------------------------------------------------------------------------
-- Canonical receipts.

record BoundaryReceipt : Set where
  constructor boundaryReceipt
  field
    receiptLabel :
      String

    receiptInspection :
      InspectionLevel

    receiptKind :
      BoundaryKind

    receiptResidual :
      BoundaryResidual

    receiptResidualIsKindResidual :
      receiptResidual ≡ boundaryKindResidual receiptKind

    receiptFourResidual :
      Residual.ResidualLevel

    receiptFourResidualIsCanonical :
      receiptFourResidual ≡ boundaryResidualToFour receiptResidual

    receiptSixResidual :
      Residual.SixResidualLevel

    receiptSixResidualIsCanonical :
      receiptSixResidual ≡ boundaryResidualToSix receiptResidual

    receiptSeverity :
      Nat

    receiptSeverityIsCanonical :
      receiptSeverity ≡ boundarySeverity receiptResidual

    receiptFibreRelation :
      FibreRelation

    receiptFibreRelationIsCanonical :
      receiptFibreRelation ≡ boundaryKindFibreRelation receiptKind

    receiptBridgeRequirement :
      BridgeRequirement

    receiptBridgeRequirementIsCanonical :
      receiptBridgeRequirement ≡ boundaryKindBridgeRequirement receiptKind

    receiptAdmissible :
      Bool

    receiptAdmissibleIsCanonical :
      receiptAdmissible
      ≡
      boundaryComparisonAdmissible
        receiptFibreRelation
        receiptBridgeRequirement
        receiptResidual

    receiptTruthPromotion :
      Bool

    receiptTruthPromotionIsFalse :
      receiptTruthPromotion ≡ false

    receiptSupportPromotion :
      Bool

    receiptSupportPromotionIsFalse :
      receiptSupportPromotion ≡ false

    receiptExternalAuthorityPromotion :
      Bool

    receiptExternalAuthorityPromotionIsFalse :
      receiptExternalAuthorityPromotion ≡ false

open BoundaryReceipt public

canonicalBoundaryReceipt :
  String →
  InspectionLevel →
  BoundaryKind →
  BoundaryReceipt
canonicalBoundaryReceipt label inspection kind =
  boundaryReceipt
    label
    inspection
    kind
    (boundaryKindResidual kind)
    refl
    (boundaryResidualToFour (boundaryKindResidual kind))
    refl
    (boundaryResidualToSix (boundaryKindResidual kind))
    refl
    (boundarySeverity (boundaryKindResidual kind))
    refl
    (boundaryKindFibreRelation kind)
    refl
    (boundaryKindBridgeRequirement kind)
    refl
    (boundaryKindAdmissible kind)
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalExactReceipt :
  BoundaryReceipt
canonicalExactReceipt =
  canonicalBoundaryReceipt
    "canonical-exact-same-fibre"
    currentStructuralInspection
    exactBoundary

canonicalPartialReceipt :
  BoundaryReceipt
canonicalPartialReceipt =
  canonicalBoundaryReceipt
    "canonical-partial-same-fibre"
    currentStructuralInspection
    partialBoundary

canonicalNoTypedMeetReceipt :
  BoundaryReceipt
canonicalNoTypedMeetReceipt =
  canonicalBoundaryReceipt
    "canonical-no-typed-meet-same-fibre"
    currentStructuralInspection
    noTypedMeetBoundary

canonicalContradictionReceipt :
  BoundaryReceipt
canonicalContradictionReceipt =
  canonicalBoundaryReceipt
    "canonical-contradiction-same-fibre"
    currentStructuralInspection
    contradictionBoundary

canonicalScopeExceededReceipt :
  BoundaryReceipt
canonicalScopeExceededReceipt =
  canonicalBoundaryReceipt
    "canonical-scope-exceeded-cross-fibre"
    bridgeAwareInspection
    scopeExceededBoundary

canonicalBoundaryReceipts :
  List BoundaryReceipt
canonicalBoundaryReceipts =
  canonicalExactReceipt
  ∷ canonicalPartialReceipt
  ∷ canonicalNoTypedMeetReceipt
  ∷ canonicalContradictionReceipt
  ∷ canonicalScopeExceededReceipt
  ∷ []

boundaryReceiptGenericReceipt :
  BoundaryReceipt →
  GenericReceipt.GenericReceipt
boundaryReceiptGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    (receiptLabel receipt)
    "DASHI.Interop.ResidualBoundaryCore"
    "canonicalBoundaryReceipts"
    "residual boundary receipt records exact, partial, no typed meet, scope exceeded, or contradiction status with canonical severity and bridge requirements"
    "residual boundary receipts do not promote truth, support, or external authority"
    "agda -i . DASHI/Interop/ResidualBoundaryCore.agda"

canonicalBoundaryGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalBoundaryGenericReceipts =
  boundaryReceiptGenericReceipt canonicalExactReceipt
  ∷ boundaryReceiptGenericReceipt canonicalPartialReceipt
  ∷ boundaryReceiptGenericReceipt canonicalNoTypedMeetReceipt
  ∷ boundaryReceiptGenericReceipt canonicalContradictionReceipt
  ∷ boundaryReceiptGenericReceipt canonicalScopeExceededReceipt
  ∷ []

canonicalBoundaryGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting canonicalBoundaryGenericReceipts
canonicalBoundaryGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting canonicalBoundaryGenericReceipts
