module DASHI.Physics.Closure.EmpiricalAdequacyCarrierDiagnostic where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface as PEMS
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2TailLiftAudit as TAIL
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2WitnessAudit as CHI2
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C

------------------------------------------------------------------------
-- W3 empirical adequacy carrier diagnostic.
--
-- This module makes the current state explicit:
--
-- * there is a small typed equality for the packaged photonuclear observable
--   profile over the shift pressure fixed point;
-- * the chi2 pool and B4 shell comparison still do not promote to the stronger
--   origin/fixed-point empirical adequacy bridge.

packagedPhotonuclearObs :
  SPTI.ShiftPressurePoint →
  PEMS.PhotonuclearMeasuredObservables Nat
packagedPhotonuclearObs _ =
  DDSI.photonuclearMeasuredObservablesNat

packagedPhotonuclearEmpirical :
  PEMS.PhotonuclearMeasuredObservables Nat
packagedPhotonuclearEmpirical =
  DDSI.photonuclearMeasuredObservablesNat

packagedPhotonuclearAdequacy :
  P0.EmpiricalAdequacy
    {SPTI.ShiftPressurePoint}
    {PEMS.PhotonuclearMeasuredObservables Nat}
packagedPhotonuclearAdequacy =
  record
    { fixedPoint = SPTI.shiftHeldExitPoint
    ; obs = packagedPhotonuclearObs
    ; empirical = packagedPhotonuclearEmpirical
    ; matches = refl
    }

data EmpiricalAdequacyCarrierMismatch : Set where
  chi2PoolCarrierMismatch : EmpiricalAdequacyCarrierMismatch
  chi2TailLiftNoSameSurface : EmpiricalAdequacyCarrierMismatch
  b4StandaloneOnly : EmpiricalAdequacyCarrierMismatch
  noOriginFixedPointObservationMap : EmpiricalAdequacyCarrierMismatch

record StrongEmpiricalAdequacyBridgeNextType : Set₁ where
  field
    adequacy :
      P0.EmpiricalAdequacy
        {SPTI.ShiftPressurePoint}
        {PEMS.PhotonuclearMeasuredObservables Nat}

    -- These are intentionally left as typed requirements.  The current repo
    -- has no theorem making the chi2 pool and B4 candidate admissible on the
    -- same fixed-point empirical carrier.
    chi2PoolTransportedToFixedPointCarrier : Set
    b4CandidatePromoted :
      B4C.B4ShellComparisonReport.promotionStatus B4C.report
      ≡
      B4C.admissibleReady
    originObservationMapCoherent : Set

record W3EmpiricalAdequacyCarrierDiagnostic : Setω where
  field
    packagedCarrier : Set
    packagedObservationCarrier : Set
    packagedEquality :
      P0.EmpiricalAdequacy
        {packagedCarrier}
        {packagedObservationCarrier}

    photonuclearValidation :
      PEVS.PhotonuclearEmpiricalValidationSummary Nat
    photonuclearBoundaryHeld :
      PEVS.PhotonuclearEmpiricalValidationSummary.nonClaimBoundary
        photonuclearValidation
      ≡
      PEVS.empiricalOnlyValidation

    chi2Audit :
      CHI2.ShiftContractMdlLevelChi2WitnessAudit
    chi2OutcomeIsMismatch :
      CHI2.ShiftContractMdlLevelChi2WitnessAudit.outcome chi2Audit
      ≡
      CHI2.poolCarrierMismatch

    chi2TailLiftAudit :
      TAIL.ShiftContractMdlLevelChi2TailLiftAudit
    chi2TailLiftOutcome :
      TAIL.ShiftContractMdlLevelChi2TailLiftAudit.outcome chi2TailLiftAudit
      ≡
      TAIL.noSameSurfaceRecovered

    b4ShellReport :
      B4C.B4ShellComparisonReport
    b4PromotionHeld :
      B4C.B4ShellComparisonReport.promotionStatus b4ShellReport
      ≡
      B4C.standaloneOnly

    mismatches :
      List EmpiricalAdequacyCarrierMismatch

    nextTypeNeeded :
      Set₁

w3EmpiricalAdequacyCarrierDiagnostic :
  W3EmpiricalAdequacyCarrierDiagnostic
w3EmpiricalAdequacyCarrierDiagnostic =
  record
    { packagedCarrier = SPTI.ShiftPressurePoint
    ; packagedObservationCarrier =
        PEMS.PhotonuclearMeasuredObservables Nat
    ; packagedEquality = packagedPhotonuclearAdequacy
    ; photonuclearValidation = DDSI.photonuclearValidationSummaryNat
    ; photonuclearBoundaryHeld = refl
    ; chi2Audit = CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit
    ; chi2OutcomeIsMismatch = refl
    ; chi2TailLiftAudit =
        TAIL.canonicalShiftContractMdlLevelChi2TailLiftAudit
    ; chi2TailLiftOutcome = refl
    ; b4ShellReport = B4C.report
    ; b4PromotionHeld = refl
    ; mismatches =
        chi2PoolCarrierMismatch
        ∷ chi2TailLiftNoSameSurface
        ∷ b4StandaloneOnly
        ∷ noOriginFixedPointObservationMap
        ∷ []
    ; nextTypeNeeded = StrongEmpiricalAdequacyBridgeNextType
    }
