module DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)

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

data ExternalOriginPromotedEmpiricalStatusAuthority : Set where

record PromotedOriginEmpiricalStatusReceipt : Set where
  constructor promotedOriginEmpiricalStatusReceipt
  field
    externalStatusAuthority :
      ExternalOriginPromotedEmpiricalStatusAuthority

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

data CurrentOriginReceiptPromotedStatusImpossible : Set where

currentOriginPromotedStatusAuthorityUnavailable :
  ExternalOriginPromotedEmpiricalStatusAuthority →
  CurrentOriginReceiptPromotedStatusImpossible
currentOriginPromotedStatusAuthorityUnavailable ()

currentOriginPromotedStatusReceiptUnavailable :
  PromotedOriginEmpiricalStatusReceipt →
  CurrentOriginReceiptPromotedStatusImpossible
currentOriginPromotedStatusReceiptUnavailable receipt =
  currentOriginPromotedStatusAuthorityUnavailable
    (PromotedOriginEmpiricalStatusReceipt.externalStatusAuthority receipt)

currentOriginReceiptCannotSupplyPromotedStatus :
  P0.OriginObservationReceipt.empiricalStatus
    Origin.minimalCredibleShiftOriginObservationReceipt
  ≡
  P0.empiricalEqualityOnly
  ⊎
  P0.OriginObservationReceipt.empiricalStatus
    Origin.minimalCredibleShiftOriginObservationReceipt
  ≡
  P0.empiricalDiagnosticOnly →
  CurrentOriginReceiptPromotedStatusImpossible
currentOriginReceiptCannotSupplyPromotedStatus (inj₁ ())
currentOriginReceiptCannotSupplyPromotedStatus (inj₂ ())

currentOriginObservationMapCompatibility :
  (carrier : Origin.MinimalCredibleShiftOriginCarrier) →
  Origin.originObservationMapMinimalCredibleShift carrier
  ≡
  P0.OriginObservationReceipt.originObservationMap
    Origin.minimalCredibleShiftOriginObservationReceipt
    carrier
currentOriginObservationMapCompatibility carrier =
  refl

currentClosureBoundaryPreservation :
  Origin.MinimalCredibleShiftClosureBoundary →
  Origin.MinimalCredibleShiftClosureBoundary
currentClosureBoundaryPreservation boundary =
  boundary

currentClosureBoundaryReflectsCurrentReceipt :
  Origin.MinimalCredibleShiftClosureBoundary →
  P0.OriginObservationReceipt.closureClaimBoundary
    Origin.minimalCredibleShiftOriginObservationReceipt
currentClosureBoundaryReflectsCurrentReceipt boundary =
  boundary

------------------------------------------------------------------------
-- K8c / Gauss: source scan diagnostic.
--
-- The current repo surfaces include a surrogate `P0.EmpiricalAdequacy` over
-- the shift-pressure carrier, but no accepted origin authority or bridge that
-- promotes the concrete MinimalCredibleShift origin receipt.  The diagnostic
-- below keeps that distinction typed: the current module can eliminate any
-- attempted promoted-status receipt because such a receipt must carry the
-- constructorless external authority token.

data OriginEmpiricalAuthoritySourceScanResult : Set where
  noCurrentOriginAuthoritySourceFound :
    OriginEmpiricalAuthoritySourceScanResult

data OriginPromotionExternalReceiptNeeded : Set where
  needExternalOriginPromotedEmpiricalStatusAuthority :
    OriginPromotionExternalReceiptNeeded
  needOriginEmpiricalAdequacyBridgeForCurrentReceipt :
    OriginPromotionExternalReceiptNeeded

record CurrentOriginAuthoritySourceDiagnostic : Setω where
  field
    sourceScanResult :
      OriginEmpiricalAuthoritySourceScanResult

    currentEmpiricalStatusBlocked :
      P0.OriginObservationReceipt.empiricalStatus
        Origin.minimalCredibleShiftOriginObservationReceipt
      ≡
      P0.empiricalBlocked

    currentReceiptCannotPromoteItself :
      P0.OriginObservationReceipt.empiricalStatus
        Origin.minimalCredibleShiftOriginObservationReceipt
      ≡
      P0.empiricalEqualityOnly
      ⊎
      P0.OriginObservationReceipt.empiricalStatus
        Origin.minimalCredibleShiftOriginObservationReceipt
      ≡
      P0.empiricalDiagnosticOnly →
      CurrentOriginReceiptPromotedStatusImpossible

    promotedStatusReceiptEliminatesHere :
      PromotedOriginEmpiricalStatusReceipt →
      CurrentOriginReceiptPromotedStatusImpossible

    missingExternalAuthorityReceipt :
      OriginPromotionExternalReceiptNeeded

    missingCurrentOriginAdequacyBridge :
      OriginPromotionExternalReceiptNeeded

    acceptedSurrogateBoundary :
      String

    requiredExternalReceipt :
      String

    noPromotionBoundary :
      List String

canonicalCurrentOriginAuthoritySourceDiagnostic :
  CurrentOriginAuthoritySourceDiagnostic
canonicalCurrentOriginAuthoritySourceDiagnostic =
  record
    { sourceScanResult =
        noCurrentOriginAuthoritySourceFound
    ; currentEmpiricalStatusBlocked =
        refl
    ; currentReceiptCannotPromoteItself =
        currentOriginReceiptCannotSupplyPromotedStatus
    ; promotedStatusReceiptEliminatesHere =
        currentOriginPromotedStatusReceiptUnavailable
    ; missingExternalAuthorityReceipt =
        needExternalOriginPromotedEmpiricalStatusAuthority
    ; missingCurrentOriginAdequacyBridge =
        needOriginEmpiricalAdequacyBridgeForCurrentReceipt
    ; acceptedSurrogateBoundary =
        "surrogate or packaged empirical adequacy surfaces do not promote the MinimalCredibleShift origin receipt"
    ; requiredExternalReceipt =
        "supply ExternalOriginPromotedEmpiricalStatusAuthority or a P0.EmpiricalAdequacy bridge whose carrier/observation pair is the current MinimalCredibleShift origin receipt"
    ; noPromotionBoundary =
        "K8c found no existing repo surface that can construct the external origin promoted-status authority"
        ∷ "Any PromotedOriginEmpiricalStatusReceipt in this module eliminates through its constructorless authority field"
        ∷ "The current MinimalCredibleShift origin receipt remains empiricalBlocked"
        ∷ []
    }

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

    currentReceiptCannotPromoteItself :
      P0.OriginObservationReceipt.empiricalStatus
        Origin.minimalCredibleShiftOriginObservationReceipt
      ≡
      P0.empiricalEqualityOnly
      ⊎
      P0.OriginObservationReceipt.empiricalStatus
        Origin.minimalCredibleShiftOriginObservationReceipt
      ≡
      P0.empiricalDiagnosticOnly →
      CurrentOriginReceiptPromotedStatusImpossible

    canonicalOriginMapCompatibility :
      (carrier : Origin.MinimalCredibleShiftOriginCarrier) →
      Origin.originObservationMapMinimalCredibleShift carrier
      ≡
      P0.OriginObservationReceipt.originObservationMap
        Origin.minimalCredibleShiftOriginObservationReceipt
        carrier

    canonicalClosureBoundaryPreservation :
      Origin.MinimalCredibleShiftClosureBoundary →
      Origin.MinimalCredibleShiftClosureBoundary

    canonicalClosureBoundaryReflectsCurrentReceipt :
      Origin.MinimalCredibleShiftClosureBoundary →
      P0.OriginObservationReceipt.closureClaimBoundary
        Origin.minimalCredibleShiftOriginObservationReceipt

    currentAuthoritySourceDiagnostic :
      CurrentOriginAuthoritySourceDiagnostic

    blockedFields :
      List OriginReceiptPromotionExternalBlockedField

    requiredExternalReceipt :
      String

    promotedStatusAuthorityBoundary :
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
    ; currentReceiptCannotPromoteItself =
        currentOriginReceiptCannotSupplyPromotedStatus
    ; canonicalOriginMapCompatibility =
        currentOriginObservationMapCompatibility
    ; canonicalClosureBoundaryPreservation =
        currentClosureBoundaryPreservation
    ; canonicalClosureBoundaryReflectsCurrentReceipt =
        currentClosureBoundaryReflectsCurrentReceipt
    ; currentAuthoritySourceDiagnostic =
        canonicalCurrentOriginAuthoritySourceDiagnostic
    ; blockedFields =
        missingEmpiricalAdequacyBridgeOrPromotedStatus
        ∷ originReceiptStillEmpiricalBlocked
        ∷ []
    ; requiredExternalReceipt =
        "provide an empirical adequacy bridge or externally-authorized promoted empirical status plus origin-map compatibility and closure-boundary preservation"
    ; promotedStatusAuthorityBoundary =
        "a promoted empirical status receipt requires ExternalOriginPromotedEmpiricalStatusAuthority; this module provides no constructor for that authority"
    ; observationMapBoundary =
        "canonical current origin observation map compatibility is discharged; any external origin observation map must still agree with originObservationMapMinimalCredibleShift on the current carrier"
    ; closureBoundary =
        "canonical current closure-boundary preservation is discharged by identity; origin observation alone still does not promote closure"
    ; noPromotionBoundary =
        "This module is an external receipt obligation only"
        ∷ "The existing MinimalCredibleShift origin receipt remains empiricalBlocked"
        ∷ "No ExternalOriginPromotedEmpiricalStatusAuthority is constructed here"
        ∷ "No P0.OriginReceipt or W3 empirical adequacy bridge is constructed here"
        ∷ []
    }

canonicalOriginReceiptPromotionExternalBlockedFields :
  List OriginReceiptPromotionExternalBlockedField
canonicalOriginReceiptPromotionExternalBlockedFields =
  OriginReceiptPromotionExternalCurrentStatus.blockedFields
    canonicalOriginReceiptPromotionExternalCurrentStatus
