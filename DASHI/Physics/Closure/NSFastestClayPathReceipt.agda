module DASHI.Physics.Closure.NSFastestClayPathReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintFiftyEightNormalizedActionInflationReceipt
  as Sprint58
import DASHI.Physics.Closure.NSHminus1Over2ObstructionReceipt as HMinus
import DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt as NegSob
import DASHI.Physics.Closure.NSNonCircularKStarDriftBoundTargetReceipt as KStar

------------------------------------------------------------------------
-- Fastest honest Clay-NS path.
--
-- This receipt records the operational decision after the Sprint 56-58 packet
-- audits and the negative-Sobolev danger-shell receipts.  The packet-normalized
-- action ledger is not the shortest proof path, because Sprint 58 records it
-- as non-additive.  The fastest honest Clay-facing lane is now the
-- H^{-1/2} decision gate: either prove the non-circular high-high defect
-- estimate and route it through K* absorption, or replace the numerical
-- divergence witness with an analytic obstruction theorem and pivot.
--
-- This module does not prove the analytic PDE estimate and does not promote
-- Clay Navier-Stokes.

data NSFastestClayPathStatus : Set where
  hMinusHalfDecisionGateSelected_noPromotion :
    NSFastestClayPathStatus

data NSFastestClayPathAction : Set where
  retirePacketNormalizedActionAsProofSource :
    NSFastestClayPathAction

  decideHMinusHalfDefectGate :
    NSFastestClayPathAction

  proveNonCircularKStarAbsorptionIfGatePasses :
    NSFastestClayPathAction

  publishObstructionAndPivotIfGateFails :
    NSFastestClayPathAction

  feedOnlyAProvedGateToBKMOrSerrin :
    NSFastestClayPathAction

canonicalNSFastestClayPathActions :
  List NSFastestClayPathAction
canonicalNSFastestClayPathActions =
  retirePacketNormalizedActionAsProofSource
  ∷ decideHMinusHalfDefectGate
  ∷ proveNonCircularKStarAbsorptionIfGatePasses
  ∷ publishObstructionAndPivotIfGateFails
  ∷ feedOnlyAProvedGateToBKMOrSerrin
  ∷ []

data NSFastestClayPathOpenGate : Set where
  analyticHMinusHalfDefectBound :
    NSFastestClayPathOpenGate

  analyticScalingObstructionOrUniformBoundDecision :
    NSFastestClayPathOpenGate

  nonCircularKStarDriftContainment :
    NSFastestClayPathOpenGate

  edgeInfluxAbsorptionAtDangerShell :
    NSFastestClayPathOpenGate

  thetaPreservation :
    NSFastestClayPathOpenGate

  tailToBKMSerrinContinuation :
    NSFastestClayPathOpenGate

canonicalNSFastestClayPathOpenGates :
  List NSFastestClayPathOpenGate
canonicalNSFastestClayPathOpenGates =
  analyticHMinusHalfDefectBound
  ∷ analyticScalingObstructionOrUniformBoundDecision
  ∷ nonCircularKStarDriftContainment
  ∷ edgeInfluxAbsorptionAtDangerShell
  ∷ thetaPreservation
  ∷ tailToBKMSerrinContinuation
  ∷ []

data NSFastestClayPromotion : Set where

nsFastestClayPromotionImpossibleHere :
  NSFastestClayPromotion →
  ⊥
nsFastestClayPromotionImpossibleHere ()

fastestClayNSPathStatement : String
fastestClayNSPathStatement =
  "Fastest honest NS Clay path: retire the packet-normalized action ledger as a proof source; decide the H^{-1/2} high-high defect gate; if it passes, prove non-circular K* absorption and theta preservation, then feed a proved tail bound to BKM/Serrin; if it fails, promote only an obstruction theorem and pivot."

fastestClayNSBoundary : String
fastestClayNSBoundary =
  "This is a route-selection receipt.  It does not prove the H^{-1/2} estimate, NonCircularKStarDriftBound, theta preservation, BKM/Serrin continuation, no finite-time blowup, or Clay Navier-Stokes."

record NSFastestClayPathReceipt : Setω where
  field
    status :
      NSFastestClayPathStatus

    statusIsCanonical :
      status ≡ hMinusHalfDecisionGateSelected_noPromotion

    sprint58Receipt :
      Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt

    sprint58NoAdditivity :
      Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt.normalizedActionAdditivityProved
        sprint58Receipt
      ≡
      false

    sprint58NoWeightedSummability :
      Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt.weightedPacketActionSummabilityProved
        sprint58Receipt
      ≡
      false

    sprint58NoPhysicalBridge :
      Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt.physicalBridge
        sprint58Receipt
      ≡
      false

    hMinusReceipt :
      HMinus.NSHminus1Over2ObstructionReceipt

    hMinusDivergenceRecorded :
      HMinus.ratioDivergesAsNuToZero hMinusReceipt ≡ true

    hMinusUniformAbsorptionNotProved :
      HMinus.uniformAbsorptionEstimateProvedHere hMinusReceipt ≡ false

    hMinusNoClay :
      HMinus.clayNavierStokesPromoted hMinusReceipt ≡ false

    negativeSobolevReceipt :
      NegSob.NSNegativeSobolevDangerShellReceipt zero

    negativeSobolevTargetRecorded :
      NegSob.nonlinearDefectSpaceTargetRecorded negativeSobolevReceipt
      ≡
      true

    negativeSobolevDefectBoundOpen :
      NegSob.highHighDefectBoundProvedHere negativeSobolevReceipt
      ≡
      false

    negativeSobolevNoCircularInput :
      NegSob.hOneHalfVelocityRegularityAssumed negativeSobolevReceipt
      ≡
      false

    kStarReceipt :
      KStar.NSNonCircularKStarDriftBoundTargetReceipt

    kStarHighHighLoadBearing :
      KStar.highHighParaproductLoadBearing kStarReceipt ≡ true

    kStarNonCircularControlOpen :
      KStar.nonCircularHighHighControlProvedHere kStarReceipt ≡ false

    kStarDriftOpen :
      KStar.kStarDriftContainmentProvedHere kStarReceipt ≡ false

    kStarThetaPreservationOpen :
      KStar.thetaPreservationProvedHere kStarReceipt ≡ false

    actions :
      List NSFastestClayPathAction

    actionsAreCanonical :
      actions ≡ canonicalNSFastestClayPathActions

    openGates :
      List NSFastestClayPathOpenGate

    openGatesAreCanonical :
      openGates ≡ canonicalNSFastestClayPathOpenGates

    packetNormalizedLedgerProofPathActive :
      Bool

    packetNormalizedLedgerProofPathActiveIsFalse :
      packetNormalizedLedgerProofPathActive ≡ false

    hMinusHalfDecisionGateActive :
      Bool

    hMinusHalfDecisionGateActiveIsTrue :
      hMinusHalfDecisionGateActive ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ fastestClayNSPathStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ fastestClayNSBoundary

    promotions :
      List NSFastestClayPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSFastestClayPromotion →
      ⊥

open NSFastestClayPathReceipt public

canonicalNSFastestClayPathReceipt :
  NSFastestClayPathReceipt
canonicalNSFastestClayPathReceipt =
  record
    { status =
        hMinusHalfDecisionGateSelected_noPromotion
    ; statusIsCanonical =
        refl
    ; sprint58Receipt =
        Sprint58.canonicalSprint58Receipt
    ; sprint58NoAdditivity =
        refl
    ; sprint58NoWeightedSummability =
        refl
    ; sprint58NoPhysicalBridge =
        refl
    ; hMinusReceipt =
        HMinus.canonicalNSHminus1Over2ObstructionReceipt
    ; hMinusDivergenceRecorded =
        refl
    ; hMinusUniformAbsorptionNotProved =
        refl
    ; hMinusNoClay =
        refl
    ; negativeSobolevReceipt =
        NegSob.canonicalNSNegativeSobolevDangerShellReceipt
    ; negativeSobolevTargetRecorded =
        refl
    ; negativeSobolevDefectBoundOpen =
        refl
    ; negativeSobolevNoCircularInput =
        refl
    ; kStarReceipt =
        KStar.canonicalNSNonCircularKStarDriftBoundTargetReceipt
    ; kStarHighHighLoadBearing =
        refl
    ; kStarNonCircularControlOpen =
        refl
    ; kStarDriftOpen =
        refl
    ; kStarThetaPreservationOpen =
        refl
    ; actions =
        canonicalNSFastestClayPathActions
    ; actionsAreCanonical =
        refl
    ; openGates =
        canonicalNSFastestClayPathOpenGates
    ; openGatesAreCanonical =
        refl
    ; packetNormalizedLedgerProofPathActive =
        false
    ; packetNormalizedLedgerProofPathActiveIsFalse =
        refl
    ; hMinusHalfDecisionGateActive =
        true
    ; hMinusHalfDecisionGateActiveIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        fastestClayNSPathStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        fastestClayNSBoundary
    ; boundaryIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsFastestClayPromotionImpossibleHere
    }

canonicalNSFastestClayPathGateActive :
  hMinusHalfDecisionGateActive canonicalNSFastestClayPathReceipt ≡ true
canonicalNSFastestClayPathGateActive =
  refl

canonicalNSFastestClayPathNoClay :
  clayNavierStokesPromoted canonicalNSFastestClayPathReceipt ≡ false
canonicalNSFastestClayPathNoClay =
  refl
