module DASHI.Physics.Closure.Chi2NonForgettingSameSurfaceObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.Closure.Chi2FixedPointCarrierTransportObstruction as OLD
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2TailLiftAudit as TAIL
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2WitnessAudit as CHI2
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB

------------------------------------------------------------------------
-- W3 chi2 non-forgetting same-surface obstruction.
--
-- The existing fixed-point receipt is inhabited only because both maps forget
-- the chi2 pool.  This module spells out the stronger receipt shape W3 would
-- need and records the typed obstruction: with the current Nat defect target,
-- a same-surface observation that matches the same defect value for primary
-- and secondary cannot also distinguish those cases.

private
  _≢local_ : {A : Set} → A → A → Set
  x ≢local y = x ≡ y → ⊥

primaryCase : LIB.Chi2BoundaryCase
primaryCase =
  CHI2.primary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit

secondaryCase : LIB.Chi2BoundaryCase
secondaryCase =
  CHI2.secondary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit

tertiaryCase : LIB.Chi2BoundaryCase
tertiaryCase =
  CHI2.tertiary CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit

record Chi2NonForgettingSameSurfaceAttempt : Set where
  field
    poolToFixedPoint :
      LIB.Chi2BoundaryCase →
      SPTI.ShiftPressurePoint

    observationOnPool :
      LIB.Chi2BoundaryCase →
      Nat

    primaryLandsOnFixedPoint :
      poolToFixedPoint primaryCase
      ≡
      SPTI.shiftHeldExitPoint

    secondaryLandsOnFixedPoint :
      poolToFixedPoint secondaryCase
      ≡
      SPTI.shiftHeldExitPoint

    tertiaryLandsOnFixedPoint :
      poolToFixedPoint tertiaryCase
      ≡
      SPTI.shiftHeldExitPoint

    primaryMatchesDefectTarget :
      observationOnPool primaryCase
      ≡
      OLD.chi2FixedPointDefectTarget

    secondaryMatchesDefectTarget :
      observationOnPool secondaryCase
      ≡
      OLD.chi2FixedPointDefectTarget

    tertiaryMatchesDefectTarget :
      observationOnPool tertiaryCase
      ≡
      OLD.chi2FixedPointDefectTarget

    primarySecondaryObservedDistinct :
      observationOnPool primaryCase
      ≢local
      observationOnPool secondaryCase

nonForgettingSameNatDefectContradiction :
  Chi2NonForgettingSameSurfaceAttempt →
  ⊥
nonForgettingSameNatDefectContradiction attempt =
  Chi2NonForgettingSameSurfaceAttempt.primarySecondaryObservedDistinct
    attempt
    (trans
      (Chi2NonForgettingSameSurfaceAttempt.primaryMatchesDefectTarget attempt)
      (sym
        (Chi2NonForgettingSameSurfaceAttempt.secondaryMatchesDefectTarget
          attempt)))

data Chi2NonForgettingMissingIngredient : Set where
  missingChi2BoundaryCaseDiscriminator :
    Chi2NonForgettingMissingIngredient
  missingInjectiveChi2BoundaryObservation :
    Chi2NonForgettingMissingIngredient
  missingSameSurfaceTransportLawOverChi2BoundaryCase :
    Chi2NonForgettingMissingIngredient
  missingNonconstantEmpiricalObservationTarget :
    Chi2NonForgettingMissingIngredient

data Chi2NonForgettingSameSurfaceStatus : Set where
  blockedBySameNatDefectAndCarrierForgettingReceipt :
    Chi2NonForgettingSameSurfaceStatus

record Chi2NonForgettingSameSurfaceObstruction : Set where
  field
    currentCarrierForgettingReceipt :
      OLD.Chi2FixedPointCarrierTransportReceipt

    currentReceiptBoundary :
      OLD.Chi2FixedPointCarrierTransportReceiptBoundary

    nonForgettingAttemptContradictsSameNatDefect :
      Chi2NonForgettingSameSurfaceAttempt →
      ⊥

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

    missingCaseDiscriminator :
      Chi2NonForgettingMissingIngredient

    missingInjectiveObservation :
      Chi2NonForgettingMissingIngredient

    missingSameSurfaceTransportLaw :
      Chi2NonForgettingMissingIngredient

    missingNonconstantObservationTarget :
      Chi2NonForgettingMissingIngredient

    status :
      Chi2NonForgettingSameSurfaceStatus

canonicalChi2NonForgettingSameSurfaceObstruction :
  Chi2NonForgettingSameSurfaceObstruction
canonicalChi2NonForgettingSameSurfaceObstruction =
  record
    { currentCarrierForgettingReceipt =
        OLD.canonicalChi2FixedPointCarrierTransportReceipt
    ; currentReceiptBoundary =
        OLD.carrierForgettingConstantReceiptOnly
    ; nonForgettingAttemptContradictsSameNatDefect =
        nonForgettingSameNatDefectContradiction
    ; poolAuditStillCarrierMismatched = refl
    ; tailLiftStillNoSameSurface = refl
    ; missingCaseDiscriminator =
        missingChi2BoundaryCaseDiscriminator
    ; missingInjectiveObservation =
        missingInjectiveChi2BoundaryObservation
    ; missingSameSurfaceTransportLaw =
        missingSameSurfaceTransportLawOverChi2BoundaryCase
    ; missingNonconstantObservationTarget =
        missingNonconstantEmpiricalObservationTarget
    ; status = blockedBySameNatDefectAndCarrierForgettingReceipt
    }

chi2NonForgettingSameSurfaceDiagnostic :
  P0.MismatchDiagnostic
chi2NonForgettingSameSurfaceDiagnostic =
  record
    { firstMismatchDepth = suc (suc zero)
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-explain
    ; causeReceipt = Chi2NonForgettingSameSurfaceObstruction
    ; causeWitness = canonicalChi2NonForgettingSameSurfaceObstruction
    }
