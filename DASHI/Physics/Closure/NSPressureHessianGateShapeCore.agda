module DASHI.Physics.Closure.NSPressureHessianGateShapeCore where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Reusable fail-closed shape core for pressure-Hessian / T(b) gate records.
--
-- This module only fixes the shared surface that later receipts may compose
-- with.  It records the sign choices, pressure-solve convention, and the
-- fail-closed audit/promotion bits, but it does not wire any theorem or
-- promote any local-to-global claim.

data GateSign : Set where
  positive :
    GateSign
  negative :
    GateSign
  zeroWithinTolerance :
    GateSign

data PressureSolveConvention : Set where
  globalEllipticSolve :
    PressureSolveConvention
  localProjectionSolve :
    PressureSolveConvention
  externalDNSCoupledSolve :
    PressureSolveConvention

record NSPressureHessianGateShapeCore : Setω where
  field
    qcritSign :
      GateSign

    localLambda2Sign :
      GateSign

    localLambda2SignIsNegative :
      localLambda2Sign ≡ negative

    pressureSolveConvention :
      PressureSolveConvention

    pressureSolveConventionIsGlobalElliptic :
      pressureSolveConvention ≡ globalEllipticSolve

    divergenceAuditRecorded :
      Bool

    divergenceAuditRecordedIsTrue :
      divergenceAuditRecorded ≡ true

    pressureHessianSignPromoted :
      Bool

    pressureHessianSignPromotedIsFalse :
      pressureHessianSignPromoted ≡ false

    externalDNSRequired :
      Bool

    externalDNSRequiredIsTrue :
      externalDNSRequired ≡ true

    localToGlobalProofPromoted :
      Bool

    localToGlobalProofPromotedIsFalse :
      localToGlobalProofPromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

open NSPressureHessianGateShapeCore public

canonicalNSPressureHessianGateShapeCore :
  NSPressureHessianGateShapeCore
canonicalNSPressureHessianGateShapeCore =
  record
    { qcritSign =
        positive
    ; localLambda2Sign =
        negative
    ; localLambda2SignIsNegative =
        refl
    ; pressureSolveConvention =
        globalEllipticSolve
    ; pressureSolveConventionIsGlobalElliptic =
        refl
    ; divergenceAuditRecorded =
        true
    ; divergenceAuditRecordedIsTrue =
        refl
    ; pressureHessianSignPromoted =
        false
    ; pressureHessianSignPromotedIsFalse =
        refl
    ; externalDNSRequired =
        true
    ; externalDNSRequiredIsTrue =
        refl
    ; localToGlobalProofPromoted =
        false
    ; localToGlobalProofPromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    }
