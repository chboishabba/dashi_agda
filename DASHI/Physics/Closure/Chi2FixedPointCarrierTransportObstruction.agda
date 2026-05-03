module DASHI.Physics.Closure.Chi2FixedPointCarrierTransportObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface as PEMS
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2TailLiftAudit as TAIL
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2WitnessAudit as CHI2
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB

------------------------------------------------------------------------
-- W3d chi2 fixed-point carrier transport obstruction.
--
-- This module names the positive receipt W3 would need, then records the
-- current canonical obstruction without promoting an empirical adequacy claim.
-- The canonical inhabitant below is deliberately marked as carrier-forgetting:
-- it proves the receipt type is too weak to discharge the same-surface theorem.

chi2FixedPointDefectTarget :
  Nat
chi2FixedPointDefectTarget =
  PEMS.PhotonuclearMeasuredObservables.defectIntensity
    DDSI.photonuclearMeasuredObservablesNat

record Chi2FixedPointCarrierTransportReceipt : Set where
  field
    poolToFixedPoint :
      LIB.Chi2BoundaryCase →
      SPTI.ShiftPressurePoint

    observationOnPool :
      LIB.Chi2BoundaryCase →
      Nat

    primaryLandsOnFixedPoint :
      poolToFixedPoint
        (CHI2.primary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit)
      ≡
      SPTI.shiftHeldExitPoint

    secondaryLandsOnFixedPoint :
      poolToFixedPoint
        (CHI2.secondary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit)
      ≡
      SPTI.shiftHeldExitPoint

    tertiaryLandsOnFixedPoint :
      poolToFixedPoint
        (CHI2.tertiary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit)
      ≡
      SPTI.shiftHeldExitPoint

    primaryMatchesDefectTarget :
      observationOnPool
        (CHI2.primary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit)
      ≡
      chi2FixedPointDefectTarget

    secondaryMatchesDefectTarget :
      observationOnPool
        (CHI2.secondary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit)
      ≡
      chi2FixedPointDefectTarget

    tertiaryMatchesDefectTarget :
      observationOnPool
        (CHI2.tertiary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit)
      ≡
      chi2FixedPointDefectTarget

canonicalChi2FixedPointCarrierTransportReceipt :
  Chi2FixedPointCarrierTransportReceipt
canonicalChi2FixedPointCarrierTransportReceipt =
  record
    { poolToFixedPoint = λ _ → SPTI.shiftHeldExitPoint
    ; observationOnPool = λ _ → chi2FixedPointDefectTarget
    ; primaryLandsOnFixedPoint = refl
    ; secondaryLandsOnFixedPoint = refl
    ; tertiaryLandsOnFixedPoint = refl
    ; primaryMatchesDefectTarget = refl
    ; secondaryMatchesDefectTarget = refl
    ; tertiaryMatchesDefectTarget = refl
    }

data Chi2FixedPointCarrierTransportReceiptBoundary : Set where
  carrierForgettingConstantReceiptOnly :
    Chi2FixedPointCarrierTransportReceiptBoundary

data Chi2FixedPointCarrierTransportMissingSurface : Set where
  missingChi2PoolToShiftPressurePointSameSurface :
    Chi2FixedPointCarrierTransportMissingSurface
  missingChi2PoolToNatDefectObservation :
    Chi2FixedPointCarrierTransportMissingSurface

data Chi2FixedPointCarrierTransportStatus : Set where
  blockedByPoolMismatchAndNoSameSurface :
    Chi2FixedPointCarrierTransportStatus

record Chi2FixedPointCarrierTransportObstruction : Set where
  field
    fixedPointTarget :
      SPTI.ShiftPressurePoint

    fixedPointTargetHeld :
      fixedPointTarget
      ≡
      SPTI.shiftHeldExitPoint

    empiricalDefectTarget :
      Nat

    poolAuditStillCarrierMismatched :
      CHI2.ShiftContractMdlLevelChi2WitnessAudit.outcome
        CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit
      ≡
      CHI2.poolCarrierMismatch

    tailLiftStillNoSameSurface :
      TAIL.ShiftContractMdlLevelChi2TailLiftAudit.outcome
        TAIL.canonicalShiftContractMdlLevelChi2TailLiftAudit
      ≡
      TAIL.noSameSurfaceRecovered

    typedReceiptAvailable :
      Chi2FixedPointCarrierTransportReceipt

    typedReceiptDoesNotDischargeSameSurface :
      Chi2FixedPointCarrierTransportReceiptBoundary

    missingSameSurfaceTheorem :
      Chi2FixedPointCarrierTransportMissingSurface

    missingObservationTheorem :
      Chi2FixedPointCarrierTransportMissingSurface

    status :
      Chi2FixedPointCarrierTransportStatus

canonicalChi2FixedPointCarrierTransportObstruction :
  Chi2FixedPointCarrierTransportObstruction
canonicalChi2FixedPointCarrierTransportObstruction =
  record
    { fixedPointTarget = SPTI.shiftHeldExitPoint
    ; fixedPointTargetHeld = refl
    ; empiricalDefectTarget = chi2FixedPointDefectTarget
    ; poolAuditStillCarrierMismatched = refl
    ; tailLiftStillNoSameSurface = refl
    ; typedReceiptAvailable =
        canonicalChi2FixedPointCarrierTransportReceipt
    ; typedReceiptDoesNotDischargeSameSurface =
        carrierForgettingConstantReceiptOnly
    ; missingSameSurfaceTheorem =
        missingChi2PoolToShiftPressurePointSameSurface
    ; missingObservationTheorem =
        missingChi2PoolToNatDefectObservation
    ; status = blockedByPoolMismatchAndNoSameSurface
    }

chi2FixedPointCarrierTransportDiagnostic :
  P0.MismatchDiagnostic
chi2FixedPointCarrierTransportDiagnostic =
  record
    { firstMismatchDepth = zero
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-graph
    ; causeReceipt = Chi2FixedPointCarrierTransportObstruction
    ; causeWitness = canonicalChi2FixedPointCarrierTransportObstruction
    }

chi2FixedPointCarrierTransportReceiptBoundaryDiagnostic :
  P0.MismatchDiagnostic
chi2FixedPointCarrierTransportReceiptBoundaryDiagnostic =
  record
    { firstMismatchDepth = suc zero
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-explain
    ; causeReceipt = Chi2FixedPointCarrierTransportReceiptBoundary
    ; causeWitness = carrierForgettingConstantReceiptOnly
    }
