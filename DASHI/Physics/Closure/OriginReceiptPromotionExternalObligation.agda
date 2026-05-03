module DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Sum using (_⊎_)

import DASHI.Physics.Closure.MinimalCredibleShiftOriginObservation as Origin
import DASHI.Physics.Closure.P0BlockadeProofObligations as P0

------------------------------------------------------------------------
-- W8c external origin-receipt promotion obligation.
--
-- MinimalCredibleShiftOriginObservation deliberately records the concrete
-- origin observation receipt as `empiricalBlocked`.  This module names the
-- narrow external receipt shape that would be needed to promote that receipt
-- beyond the blocked status and/or feed it into the W3 empirical bridge.  It
-- does not alter the existing receipt and does not construct a promotion.

record PromotedOriginEmpiricalStatusReceipt : Set where
  field
    promotedEmpiricalStatus :
      P0.EmpiricalReceiptStatus

    promotedStatusIsAdmissible :
      promotedEmpiricalStatus ≡ P0.empiricalEqualityOnly
      ⊎
      promotedEmpiricalStatus ≡ P0.empiricalDiagnosticOnly

OriginReceiptPromotionEvidence : Set₁
OriginReceiptPromotionEvidence =
  P0.EmpiricalAdequacy
    {Origin.MinimalCredibleShiftOriginCarrier}
    {Origin.MinimalCredibleShiftOriginObs}
  ⊎
  PromotedOriginEmpiricalStatusReceipt

record OriginReceiptPromotionExternalReceipt : Setω where
  field
    empiricalPromotionEvidence :
      OriginReceiptPromotionEvidence

    originObservationMap :
      Origin.MinimalCredibleShiftOriginCarrier →
      Origin.MinimalCredibleShiftOriginObs

    originObservationMapCompatibility :
      (carrier : Origin.MinimalCredibleShiftOriginCarrier) →
      originObservationMap carrier
      ≡
      Origin.originObservationMapMinimalCredibleShift carrier

    closureBoundaryCarrier :
      Set

    closureBoundaryPreservation :
      Origin.MinimalCredibleShiftClosureBoundary →
      closureBoundaryCarrier

    closureBoundaryReflectsCurrentReceipt :
      closureBoundaryCarrier →
      P0.OriginObservationReceipt.closureClaimBoundary
        Origin.minimalCredibleShiftOriginObservationReceipt

    currentOriginReceiptStillBlocked :
      P0.OriginObservationReceipt.empiricalStatus
        Origin.minimalCredibleShiftOriginObservationReceipt
      ≡
      P0.empiricalBlocked

------------------------------------------------------------------------
-- Current non-promoting status.

data OriginReceiptPromotionExternalBlockedField : Set where
  missingEmpiricalAdequacyBridgeOrPromotedStatus :
    OriginReceiptPromotionExternalBlockedField
  missingOriginObservationMapCompatibility :
    OriginReceiptPromotionExternalBlockedField
  missingClosureBoundaryPreservation :
    OriginReceiptPromotionExternalBlockedField
  originReceiptStillEmpiricalBlocked :
    OriginReceiptPromotionExternalBlockedField

record OriginReceiptPromotionExternalCurrentStatus : Setω where
  field
    originObservationReceipt :
      P0.OriginObservationReceipt

    originReceiptBlockedInstance :
      Origin.MinimalCredibleShiftBlockedOriginInstance

    currentEmpiricalStatusUnchanged :
      P0.OriginObservationReceipt.empiricalStatus
        Origin.minimalCredibleShiftOriginObservationReceipt
      ≡
      P0.empiricalBlocked

    blockedFields :
      List OriginReceiptPromotionExternalBlockedField

    requiredExternalReceipt :
      String

    observationMapBoundary :
      String

    closureBoundary :
      String

    noPromotionBoundary :
      List String

canonicalOriginReceiptPromotionExternalCurrentStatus :
  OriginReceiptPromotionExternalCurrentStatus
canonicalOriginReceiptPromotionExternalCurrentStatus =
  record
    { originObservationReceipt =
        Origin.minimalCredibleShiftOriginObservationReceipt
    ; originReceiptBlockedInstance =
        Origin.minimalCredibleShiftBlockedOriginInstanceValue
    ; currentEmpiricalStatusUnchanged =
        refl
    ; blockedFields =
        missingEmpiricalAdequacyBridgeOrPromotedStatus
        ∷ missingOriginObservationMapCompatibility
        ∷ missingClosureBoundaryPreservation
        ∷ originReceiptStillEmpiricalBlocked
        ∷ []
    ; requiredExternalReceipt =
        "provide an empirical adequacy bridge or promoted empirical status plus origin-map compatibility and closure-boundary preservation"
    ; observationMapBoundary =
        "external origin observation map must agree with originObservationMapMinimalCredibleShift on the current carrier"
    ; closureBoundary =
        "external promotion must preserve the current closure-claim boundary; origin observation alone does not promote closure"
    ; noPromotionBoundary =
        "This module is an external receipt obligation only"
        ∷ "The existing MinimalCredibleShift origin receipt remains empiricalBlocked"
        ∷ "No P0.OriginReceipt or W3 empirical adequacy bridge is constructed here"
        ∷ []
    }

canonicalOriginReceiptPromotionExternalBlockedFields :
  List OriginReceiptPromotionExternalBlockedField
canonicalOriginReceiptPromotionExternalBlockedFields =
  OriginReceiptPromotionExternalCurrentStatus.blockedFields
    canonicalOriginReceiptPromotionExternalCurrentStatus
