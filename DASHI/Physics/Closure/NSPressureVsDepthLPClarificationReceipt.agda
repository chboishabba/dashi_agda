module DASHI.Physics.Closure.NSPressureVsDepthLPClarificationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)

import DASHI.Physics.Closure.PressureDepthLengthTripleReceipt as Triple

------------------------------------------------------------------------
-- NS pressure/depth Littlewood-Paley clarification.
--
-- This receipt consumes the pressure/depth/length triple and corrects the
-- Paper 1 wording around the LP identity, theta, and danger shell.  The LP
-- identity targets the pressure accumulation/absorption balance at fixed K;
-- depth is the accumulated resolved carry history.  No Clay promotion is
-- available here.

data NSPressureDepthClarificationStatus : Set where
  pressureDepthLPTargetClarified_noClayPromotion :
    NSPressureDepthClarificationStatus

data LPClarificationPoint : Set where
  lpIdentityTargetsDepthAccumulationRate :
    LPClarificationPoint

  thetaIsPressureCreationAbsorptionRatio :
    LPClarificationPoint

  pressureAndDepthAreNotInterchangeable :
    LPClarificationPoint

  tailEnergyGrowthCompatibleWithPressureDecrease :
    LPClarificationPoint

  dangerShellActsOnPressureNotDepth :
    LPClarificationPoint

canonicalLPClarificationPoints :
  List LPClarificationPoint
canonicalLPClarificationPoints =
  lpIdentityTargetsDepthAccumulationRate
  ∷ thetaIsPressureCreationAbsorptionRatio
  ∷ pressureAndDepthAreNotInterchangeable
  ∷ tailEnergyGrowthCompatibleWithPressureDecrease
  ∷ dangerShellActsOnPressureNotDepth
  ∷ []

data DangerShellCorrectedTarget : Set where
  pressureDerivativeNonpositiveAtDangerShell :
    DangerShellCorrectedTarget

data BKMOrSerrinBridgeRequirement : Set where
  thetaStrictlyBelowOne :
    BKMOrSerrinBridgeRequirement

  kStarNotDriftingIntoInertialRange :
    BKMOrSerrinBridgeRequirement

canonicalBKMOrSerrinBridgeRequirements :
  List BKMOrSerrinBridgeRequirement
canonicalBKMOrSerrinBridgeRequirements =
  thetaStrictlyBelowOne
  ∷ kStarNotDriftingIntoInertialRange
  ∷ []

data NSPressureDepthOpenObligation : Set where
  proveKStarDriftCondition :
    NSPressureDepthOpenObligation

  provePressureDangerShellMaximumPrinciple :
    NSPressureDepthOpenObligation

canonicalNSPressureDepthOpenObligations :
  List NSPressureDepthOpenObligation
canonicalNSPressureDepthOpenObligations =
  proveKStarDriftCondition
  ∷ provePressureDangerShellMaximumPrinciple
  ∷ []

record K*DriftCondition : Set₁ where
  field
    K*ofT :
      Nat

    K*ofNu :
      Nat

    driftInequalityTarget :
      Set

    driftInequalityTargetIsK*ofT≤K*ofNu :
      driftInequalityTarget ≡ (K*ofT ≤ K*ofNu)

    recordedAsOpenObligation :
      Bool

    recordedAsOpenObligationIsTrue :
      recordedAsOpenObligation ≡ true

    dischargedHere :
      Bool

    dischargedHereIsFalse :
      dischargedHere ≡ false

open K*DriftCondition public

canonicalK*DriftCondition :
  K*DriftCondition
canonicalK*DriftCondition =
  record
    { K*ofT =
        zero
    ; K*ofNu =
        zero
    ; driftInequalityTarget =
        zero ≤ zero
    ; driftInequalityTargetIsK*ofT≤K*ofNu =
        refl
    ; recordedAsOpenObligation =
        true
    ; recordedAsOpenObligationIsTrue =
        refl
    ; dischargedHere =
        false
    ; dischargedHereIsFalse =
        refl
    }

data NSPressureDepthClarificationPromotion : Set where

nsPressureDepthClarificationPromotionImpossibleHere :
  NSPressureDepthClarificationPromotion →
  ⊥
nsPressureDepthClarificationPromotionImpossibleHere ()

lpTargetClarificationText :
  String
lpTargetClarificationText =
  "The fixed-K LP identity is read as a depth accumulation rate target: pressure is created or absorbed, while resolved absorption accumulates as depth."

thetaClarificationText :
  String
thetaClarificationText =
  "Theta is the pressure creation/absorption ratio, not a depth variable."

dangerShellCorrectedText :
  String
dangerShellCorrectedText =
  "The corrected danger-shell maximum-principle target is d/dt P(K*,t) <= 0, not d/dt D(K*,t) <= 0."

bkmSerrinBridgeCorrectedText :
  String
bkmSerrinBridgeCorrectedText =
  "The corrected BKM/Serrin bridge requires theta<1 plus K*(t) not drifting into the inertial range, recorded as K*(t) <= K*(nu)."

record NSPressureVsDepthLPClarificationReceipt : Setω where
  field
    pressureDepthLengthTriple :
      Triple.PressureDepthLengthTripleReceipt

    pressureDepthLengthTripleNoClay :
      Triple.clayPromotion pressureDepthLengthTriple ≡ false

    status :
      NSPressureDepthClarificationStatus

    statusIsCanonical :
      status ≡ pressureDepthLPTargetClarified_noClayPromotion

    clarificationPoints :
      List LPClarificationPoint

    clarificationPointsAreCanonical :
      clarificationPoints ≡ canonicalLPClarificationPoints

    dangerShellTarget :
      DangerShellCorrectedTarget

    dangerShellTargetIsPressureDerivative :
      dangerShellTarget ≡ pressureDerivativeNonpositiveAtDangerShell

    bridgeRequirements :
      List BKMOrSerrinBridgeRequirement

    bridgeRequirementsAreCanonical :
      bridgeRequirements ≡ canonicalBKMOrSerrinBridgeRequirements

    k*DriftCondition :
      K*DriftCondition

    k*DriftConditionIsCanonical :
      k*DriftCondition ≡ canonicalK*DriftCondition

    openObligations :
      List NSPressureDepthOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalNSPressureDepthOpenObligations

    lpTargetClarification :
      String

    lpTargetClarificationIsCanonical :
      lpTargetClarification ≡ lpTargetClarificationText

    thetaClarification :
      String

    thetaClarificationIsCanonical :
      thetaClarification ≡ thetaClarificationText

    dangerShellCorrectedStatement :
      String

    dangerShellCorrectedStatementIsCanonical :
      dangerShellCorrectedStatement ≡ dangerShellCorrectedText

    bkmSerrinBridgeCorrectedStatement :
      String

    bkmSerrinBridgeCorrectedStatementIsCanonical :
      bkmSerrinBridgeCorrectedStatement ≡ bkmSerrinBridgeCorrectedText

    tailEnergyCanGrowWhilePressureDecreases :
      Bool

    tailEnergyCanGrowWhilePressureDecreasesIsTrue :
      tailEnergyCanGrowWhilePressureDecreases ≡ true

    dangerShellMaxPrincipleTargetClarified :
      Bool

    dangerShellMaxPrincipleTargetClarifiedIsTrue :
      dangerShellMaxPrincipleTargetClarified ≡ true

    lpIdentityIsPressureNotDepthIdentity :
      Bool

    lpIdentityIsPressureNotDepthIdentityIsTrue :
      lpIdentityIsPressureNotDepthIdentity ≡ true

    k*DriftConditionDischarged :
      Bool

    k*DriftConditionDischargedIsFalse :
      k*DriftConditionDischarged ≡ false

    bkmSerrinBridgeClosed :
      Bool

    bkmSerrinBridgeClosedIsFalse :
      bkmSerrinBridgeClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSPressureDepthClarificationPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSPressureDepthClarificationPromotion →
      ⊥

open NSPressureVsDepthLPClarificationReceipt public

canonicalNSPressureVsDepthLPClarificationReceipt :
  NSPressureVsDepthLPClarificationReceipt
canonicalNSPressureVsDepthLPClarificationReceipt =
  record
    { pressureDepthLengthTriple =
        Triple.canonicalPressureDepthLengthTripleReceipt
    ; pressureDepthLengthTripleNoClay =
        refl
    ; status =
        pressureDepthLPTargetClarified_noClayPromotion
    ; statusIsCanonical =
        refl
    ; clarificationPoints =
        canonicalLPClarificationPoints
    ; clarificationPointsAreCanonical =
        refl
    ; dangerShellTarget =
        pressureDerivativeNonpositiveAtDangerShell
    ; dangerShellTargetIsPressureDerivative =
        refl
    ; bridgeRequirements =
        canonicalBKMOrSerrinBridgeRequirements
    ; bridgeRequirementsAreCanonical =
        refl
    ; k*DriftCondition =
        canonicalK*DriftCondition
    ; k*DriftConditionIsCanonical =
        refl
    ; openObligations =
        canonicalNSPressureDepthOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; lpTargetClarification =
        lpTargetClarificationText
    ; lpTargetClarificationIsCanonical =
        refl
    ; thetaClarification =
        thetaClarificationText
    ; thetaClarificationIsCanonical =
        refl
    ; dangerShellCorrectedStatement =
        dangerShellCorrectedText
    ; dangerShellCorrectedStatementIsCanonical =
        refl
    ; bkmSerrinBridgeCorrectedStatement =
        bkmSerrinBridgeCorrectedText
    ; bkmSerrinBridgeCorrectedStatementIsCanonical =
        refl
    ; tailEnergyCanGrowWhilePressureDecreases =
        true
    ; tailEnergyCanGrowWhilePressureDecreasesIsTrue =
        refl
    ; dangerShellMaxPrincipleTargetClarified =
        true
    ; dangerShellMaxPrincipleTargetClarifiedIsTrue =
        refl
    ; lpIdentityIsPressureNotDepthIdentity =
        true
    ; lpIdentityIsPressureNotDepthIdentityIsTrue =
        refl
    ; k*DriftConditionDischarged =
        false
    ; k*DriftConditionDischargedIsFalse =
        refl
    ; bkmSerrinBridgeClosed =
        false
    ; bkmSerrinBridgeClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsPressureDepthClarificationPromotionImpossibleHere
    }

canonicalNSPressureDepthTargetClarified :
  dangerShellMaxPrincipleTargetClarified
    canonicalNSPressureVsDepthLPClarificationReceipt
  ≡ true
canonicalNSPressureDepthTargetClarified =
  refl

canonicalNSLPIdentityPressureNotDepth :
  lpIdentityIsPressureNotDepthIdentity
    canonicalNSPressureVsDepthLPClarificationReceipt
  ≡ true
canonicalNSLPIdentityPressureNotDepth =
  refl

canonicalNSPressureDepthNoClayPromotion :
  clayNavierStokesPromoted canonicalNSPressureVsDepthLPClarificationReceipt
  ≡ false
canonicalNSPressureDepthNoClayPromotion =
  refl
