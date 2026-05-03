module DASHI.Physics.Closure.EmpiricalAdequacyCarrierDiagnostic where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as RETARGET
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision as POLICY
open import DASHI.Physics.Closure.Chi2CanonicalPoolObservationCandidate as CHI2POOL
open import DASHI.Physics.Closure.Chi2FixedPointCarrierTransportObstruction as CHI2TRANSPORT
open import DASHI.Physics.Closure.Chi2NonForgettingSameSurfaceObstruction as CHI2NF
open import DASHI.Physics.Closure.Chi2ToShiftPressureTransportCandidate as CHI2SHIFT
open import DASHI.Physics.Closure.Chi2TransportDynamicsToFixedPointBridge as CHI2DYN
open import DASHI.Physics.Closure.MinimalCredibleShiftOriginObservation as ORIGIN
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface as PEMS
open import DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary as PEVS
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2TailLiftAudit as TAIL
open import DASHI.Physics.Closure.ShiftContractMdlLevelChi2WitnessAudit as CHI2
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge as B4PB
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C

------------------------------------------------------------------------
-- W3 empirical adequacy carrier diagnostic.
--
-- This module makes the current state explicit:
--
-- * there is a small typed equality for the packaged photonuclear defect
--   observable over the shift pressure fixed point;
-- * the chi2 pool and B4 shell comparison still do not promote to the stronger
--   origin/fixed-point empirical adequacy bridge.
-- * the chi2 non-forgetting same-surface attempt is now explicitly obstructed:
--   the current single Nat defect target cannot also distinguish the primary
--   and secondary chi2 cases.
-- * the canonical chi2 pool now has a local nonconstant observation candidate,
--   but that candidate is explicitly non-empirical and non-promoting.
-- * the pool also has a local nonconstant transport candidate onto the
--   three-point shift-pressure carrier, but not all cases land on the fixed
--   point and no empirical bridge is claimed.
-- * composing that local transport with shift dynamics yields fixed-point
--   absorption within two steps, but still no empirical observation target.

packagedPhotonuclearDefectObs :
  SPTI.ShiftPressurePoint →
  Nat
packagedPhotonuclearDefectObs _ =
  PEMS.PhotonuclearMeasuredObservables.defectIntensity
    DDSI.photonuclearMeasuredObservablesNat

packagedPhotonuclearDefectEmpirical :
  Nat
packagedPhotonuclearDefectEmpirical =
  PEMS.PhotonuclearMeasuredObservables.defectIntensity
    DDSI.photonuclearMeasuredObservablesNat

packagedPhotonuclearDefectAdequacy :
  P0.EmpiricalAdequacy
    {SPTI.ShiftPressurePoint}
    {Nat}
packagedPhotonuclearDefectAdequacy =
  record
    { fixedPoint = SPTI.shiftHeldExitPoint
    ; obs = packagedPhotonuclearDefectObs
    ; empirical = packagedPhotonuclearDefectEmpirical
    ; matches = refl
    }

data EmpiricalAdequacyCarrierMismatch : Set where
  chi2PoolCarrierMismatch : EmpiricalAdequacyCarrierMismatch
  chi2TailLiftNoSameSurface : EmpiricalAdequacyCarrierMismatch
  chi2FixedPointCarrierTransportBlocked :
    EmpiricalAdequacyCarrierMismatch
  chi2FixedPointReceiptCarrierForgettingOnly :
    EmpiricalAdequacyCarrierMismatch
  chi2NonForgettingSameSurfaceObstructed :
    EmpiricalAdequacyCarrierMismatch
  chi2LocalPoolObservationCandidateOnly :
    EmpiricalAdequacyCarrierMismatch
  chi2LocalShiftPressureTransportCandidateOnly :
    EmpiricalAdequacyCarrierMismatch
  chi2LocalTransportDynamicsOnly :
    EmpiricalAdequacyCarrierMismatch
  b4StandaloneOnly : EmpiricalAdequacyCarrierMismatch
  b4ClosurePromotionSeparateFromEmpiricalValidation : EmpiricalAdequacyCarrierMismatch
  fullPhotonuclearProfileLivesInSet1 : EmpiricalAdequacyCarrierMismatch
  originObservationReceiptEmpiricalBlocked : EmpiricalAdequacyCarrierMismatch

data EmpiricalB4ValidationDischargeBlocked : Set where

standaloneOnlyNotAdmissibleReady :
  B4C.standaloneOnly ≡ B4C.admissibleReady →
  EmpiricalB4ValidationDischargeBlocked
standaloneOnlyNotAdmissibleReady ()

currentB4EmpiricalPromotionNotDischarged :
  B4C.B4ShellComparisonReport.promotionStatus B4C.report
  ≡
  B4C.admissibleReady →
  EmpiricalB4ValidationDischargeBlocked
currentB4EmpiricalPromotionNotDischarged ()

record B4EmpiricalDependencyReceipt : Set where
  field
    empiricalShellComparisonStillStandalone :
      B4C.B4ShellComparisonReport.promotionStatus B4C.report
      ≡
      B4C.standaloneOnly

    closureObservablePromotionReady :
      B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
      ≡
      B4PB.admissiblePromotionReady

    closurePromotionDoesNotDischargeEmpiricalValidation :
      B4C.B4ShellComparisonReport.promotionStatus B4C.report
      ≡
      B4C.admissibleReady →
      EmpiricalB4ValidationDischargeBlocked

b4EmpiricalDependencyReceipt :
  B4EmpiricalDependencyReceipt
b4EmpiricalDependencyReceipt =
  record
    { empiricalShellComparisonStillStandalone = refl
    ; closureObservablePromotionReady = refl
    ; closurePromotionDoesNotDischargeEmpiricalValidation =
        currentB4EmpiricalPromotionNotDischarged
    }

w1RetargetPolicyDecisionConsumed :
  RETARGET.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted
w1RetargetPolicyDecisionConsumed =
  POLICY.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted

w8bOriginObservationReceiptEmpiricalBlocked :
  P0.OriginObservationReceipt.empiricalStatus
    ORIGIN.minimalCredibleShiftOriginObservationReceipt
  ≡
  P0.empiricalBlocked
w8bOriginObservationReceiptEmpiricalBlocked =
  refl

chi2PoolMismatchDiagnostic :
  P0.MismatchDiagnostic
chi2PoolMismatchDiagnostic =
  record
    { firstMismatchDepth = zero
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-graph
    ; causeReceipt =
        CHI2.ShiftContractMdlLevelChi2WitnessAudit.outcome
          CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit
        ≡
        CHI2.poolCarrierMismatch
    ; causeWitness = refl
    }

chi2TailLiftMismatchDiagnostic :
  P0.MismatchDiagnostic
chi2TailLiftMismatchDiagnostic =
  record
    { firstMismatchDepth = suc zero
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-graph
    ; causeReceipt =
        TAIL.ShiftContractMdlLevelChi2TailLiftAudit.outcome
          TAIL.canonicalShiftContractMdlLevelChi2TailLiftAudit
        ≡
        TAIL.noSameSurfaceRecovered
    ; causeWitness = refl
    }

b4StandaloneMismatchDiagnostic :
  P0.MismatchDiagnostic
b4StandaloneMismatchDiagnostic =
  record
    { firstMismatchDepth = suc (suc zero)
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-promote
    ; causeReceipt =
        B4C.B4ShellComparisonReport.promotionStatus B4C.report
        ≡
        B4C.standaloneOnly
    ; causeWitness = refl
    }

b4ClosurePromotionSeparationDiagnostic :
  P0.MismatchDiagnostic
b4ClosurePromotionSeparationDiagnostic =
  record
    { firstMismatchDepth = suc (suc (suc zero))
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-promote
    ; causeReceipt = B4EmpiricalDependencyReceipt
    ; causeWitness = b4EmpiricalDependencyReceipt
    }

fullProfileUniverseMismatchDiagnostic :
  P0.MismatchDiagnostic
fullProfileUniverseMismatchDiagnostic =
  record
    { firstMismatchDepth = suc (suc (suc (suc zero)))
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-explain
    ; causeReceipt = EmpiricalAdequacyCarrierMismatch
    ; causeWitness = fullPhotonuclearProfileLivesInSet1
    }

originObservationReceiptBlockedDiagnostic :
  P0.MismatchDiagnostic
originObservationReceiptBlockedDiagnostic =
  record
    { firstMismatchDepth = suc (suc (suc (suc (suc zero))))
    ; modelTrit = P0.tritZero
    ; empiricalTrit = P0.tritPos
    ; mismatchKind = P0.underPromotedPos
    ; cause = P0.F-explain
    ; causeReceipt =
        P0.OriginObservationReceipt.empiricalStatus
          ORIGIN.minimalCredibleShiftOriginObservationReceipt
        ≡
        P0.empiricalBlocked
    ; causeWitness = w8bOriginObservationReceiptEmpiricalBlocked
    }

record StrongEmpiricalAdequacyBridgeNextType : Set₁ where
  field
    adequacy :
      P0.EmpiricalAdequacy
        {SPTI.ShiftPressurePoint}
        {Nat}

    -- These are intentionally left as typed requirements.  The current repo
    -- has no theorem making the chi2 pool and B4 candidate admissible on the
    -- same fixed-point empirical carrier.  The full photonuclear observable
    -- record is also universe-mismatched for the current P0 obligation
    -- because `PhotonuclearMeasuredObservables Nat : Set₁`, while
    -- `P0.EmpiricalAdequacy` quantifies over `Obs : Set`.
    chi2PoolTransportedToFixedPointCarrier :
      CHI2TRANSPORT.Chi2FixedPointCarrierTransportReceipt
    chi2PoolTransportBoundaryStillBlocked :
      CHI2TRANSPORT.Chi2FixedPointCarrierTransportReceiptBoundary
    b4CandidatePromoted :
      B4C.B4ShellComparisonReport.promotionStatus B4C.report
      ≡
      B4C.admissibleReady
    b4ClosurePromotionSeparation :
      B4EmpiricalDependencyReceipt
    originObservationReceiptPromotedFromBlocked : Set

data StrongEmpiricalAdequacyBridgeNextTypeNeeded : Set where
  strongEmpiricalAdequacyBridgeNextTypeNeeded :
    StrongEmpiricalAdequacyBridgeNextTypeNeeded

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

    chi2FixedPointCarrierTransportObstruction :
      CHI2TRANSPORT.Chi2FixedPointCarrierTransportObstruction
    chi2FixedPointCarrierTransportReceipt :
      CHI2TRANSPORT.Chi2FixedPointCarrierTransportReceipt
    chi2FixedPointCarrierTransportReceiptBoundary :
      CHI2TRANSPORT.Chi2FixedPointCarrierTransportReceiptBoundary
    chi2NonForgettingSameSurfaceObstruction :
      CHI2NF.Chi2NonForgettingSameSurfaceObstruction
    chi2CanonicalPoolObservationCandidate :
      CHI2POOL.Chi2CanonicalPoolObservationCandidate
    chi2ToShiftPressureTransportCandidate :
      CHI2SHIFT.Chi2ToShiftPressureTransportCandidate
    chi2TransportDynamicsToFixedPointBridge :
      CHI2DYN.Chi2TransportDynamicsToFixedPointBridge

    b4ShellReport :
      B4C.B4ShellComparisonReport
    b4PromotionHeld :
      B4C.B4ShellComparisonReport.promotionStatus b4ShellReport
      ≡
      B4C.standaloneOnly

    b4DependencyReceipt :
      B4EmpiricalDependencyReceipt

    retargetPolicyDecisionConsumed :
      RETARGET.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted

    originObservationReceipt :
      P0.OriginObservationReceipt
    originObservationReceiptBlocked :
      P0.OriginObservationReceipt.empiricalStatus originObservationReceipt
      ≡
      P0.empiricalBlocked
    originBlockedInstance :
      ORIGIN.MinimalCredibleShiftBlockedOriginInstance

    mismatches :
      List EmpiricalAdequacyCarrierMismatch

    structuredMismatchDiagnostics :
      List P0.MismatchDiagnostic

    nextTypeNeeded :
      StrongEmpiricalAdequacyBridgeNextTypeNeeded

w3EmpiricalAdequacyCarrierDiagnostic :
  W3EmpiricalAdequacyCarrierDiagnostic
w3EmpiricalAdequacyCarrierDiagnostic =
  record
    { packagedCarrier = SPTI.ShiftPressurePoint
    ; packagedObservationCarrier = Nat
    ; packagedEquality = packagedPhotonuclearDefectAdequacy
    ; photonuclearValidation = DDSI.photonuclearValidationSummaryNat
    ; photonuclearBoundaryHeld = refl
    ; chi2Audit = CHI2.canonicalShiftContractMdlLevelChi2WitnessAudit
    ; chi2OutcomeIsMismatch = refl
    ; chi2TailLiftAudit =
        TAIL.canonicalShiftContractMdlLevelChi2TailLiftAudit
    ; chi2TailLiftOutcome = refl
    ; chi2FixedPointCarrierTransportObstruction =
        CHI2TRANSPORT.canonicalChi2FixedPointCarrierTransportObstruction
    ; chi2FixedPointCarrierTransportReceipt =
        CHI2TRANSPORT.canonicalChi2FixedPointCarrierTransportReceipt
    ; chi2FixedPointCarrierTransportReceiptBoundary =
        CHI2TRANSPORT.carrierForgettingConstantReceiptOnly
    ; chi2NonForgettingSameSurfaceObstruction =
        CHI2NF.canonicalChi2NonForgettingSameSurfaceObstruction
    ; chi2CanonicalPoolObservationCandidate =
        CHI2POOL.canonicalChi2PoolObservationCandidate
    ; chi2ToShiftPressureTransportCandidate =
        CHI2SHIFT.canonicalChi2ToShiftPressureTransportCandidate
    ; chi2TransportDynamicsToFixedPointBridge =
        CHI2DYN.canonicalChi2TransportDynamicsToFixedPointBridge
    ; b4ShellReport = B4C.report
    ; b4PromotionHeld = refl
    ; b4DependencyReceipt = b4EmpiricalDependencyReceipt
    ; retargetPolicyDecisionConsumed = w1RetargetPolicyDecisionConsumed
    ; originObservationReceipt =
        ORIGIN.minimalCredibleShiftOriginObservationReceipt
    ; originObservationReceiptBlocked =
        w8bOriginObservationReceiptEmpiricalBlocked
    ; originBlockedInstance =
        ORIGIN.minimalCredibleShiftBlockedOriginInstanceValue
    ; mismatches =
        chi2PoolCarrierMismatch
        ∷ chi2TailLiftNoSameSurface
        ∷ chi2FixedPointCarrierTransportBlocked
        ∷ chi2FixedPointReceiptCarrierForgettingOnly
        ∷ chi2NonForgettingSameSurfaceObstructed
        ∷ chi2LocalPoolObservationCandidateOnly
        ∷ chi2LocalShiftPressureTransportCandidateOnly
        ∷ chi2LocalTransportDynamicsOnly
        ∷ b4StandaloneOnly
        ∷ b4ClosurePromotionSeparateFromEmpiricalValidation
        ∷ fullPhotonuclearProfileLivesInSet1
        ∷ originObservationReceiptEmpiricalBlocked
        ∷ []
    ; structuredMismatchDiagnostics =
        chi2PoolMismatchDiagnostic
        ∷ chi2TailLiftMismatchDiagnostic
        ∷ CHI2TRANSPORT.chi2FixedPointCarrierTransportDiagnostic
        ∷ CHI2TRANSPORT.chi2FixedPointCarrierTransportReceiptBoundaryDiagnostic
        ∷ CHI2NF.chi2NonForgettingSameSurfaceDiagnostic
        ∷ b4StandaloneMismatchDiagnostic
        ∷ b4ClosurePromotionSeparationDiagnostic
        ∷ fullProfileUniverseMismatchDiagnostic
        ∷ originObservationReceiptBlockedDiagnostic
        ∷ []
    ; nextTypeNeeded = strongEmpiricalAdequacyBridgeNextTypeNeeded
    }
