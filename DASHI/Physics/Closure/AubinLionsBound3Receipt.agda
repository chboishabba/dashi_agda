module DASHI.Physics.Closure.AubinLionsBound3Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierNSSmoothConvergenceReceipt as Smooth

------------------------------------------------------------------------
-- Bound3 prerequisite chain for the carrier Aubin-Lions route.
--
-- This receipt makes the weak time-derivative prerequisite explicit.  It
-- records the intended inputs:
--   1. Leray/L2 energy from the existing finite-depth tower receipt.
--   2. Ladyzhenskaya interpolation target for the transport term.
--   3. Diffusion dual-norm target.
--   4. Pressure-gradient dual-norm target.
--
-- The local codebase currently records these as targets, not as a completed
-- analytic estimate.  Therefore the full bound3 proof, compactness, terminal
-- smooth convergence, and Clay promotion flags remain false.

data AubinLionsBound3Prerequisite : Set where
  lerayEnergyFromFiniteTowerPrerequisite :
    AubinLionsBound3Prerequisite

  ladyzhenskayaTransportInterpolationPrerequisite :
    AubinLionsBound3Prerequisite

  diffusionDualNormPrerequisite :
    AubinLionsBound3Prerequisite

  pressureGradientDualNormPrerequisite :
    AubinLionsBound3Prerequisite

  navierStokesEquationDecompositionPrerequisite :
    AubinLionsBound3Prerequisite

canonicalAubinLionsBound3Prerequisites :
  List AubinLionsBound3Prerequisite
canonicalAubinLionsBound3Prerequisites =
  lerayEnergyFromFiniteTowerPrerequisite
  ∷ ladyzhenskayaTransportInterpolationPrerequisite
  ∷ diffusionDualNormPrerequisite
  ∷ pressureGradientDualNormPrerequisite
  ∷ navierStokesEquationDecompositionPrerequisite
  ∷ []

data AubinLionsBound3Status : Set where
  consumedFromExistingFiniteReceipt :
    AubinLionsBound3Status

  recordedAnalyticTarget :
    AubinLionsBound3Status

  recordedEquationDecompositionTarget :
    AubinLionsBound3Status

  blockedUntilFormalEstimate :
    AubinLionsBound3Status

data AubinLionsBound3EstimateTarget : Set where
  l2TimeWMinusOneTwoDerivativeBoundTarget :
    AubinLionsBound3EstimateTarget

data AubinLionsBound3Blocker : Set where
  missingFormalCompositionOfLadyzhenskayaDiffusionPressureIntoL2WMinusOneTwo :
    AubinLionsBound3Blocker

canonicalAubinLionsBound3Blockers :
  List AubinLionsBound3Blocker
canonicalAubinLionsBound3Blockers =
  missingFormalCompositionOfLadyzhenskayaDiffusionPressureIntoL2WMinusOneTwo
  ∷ []

bound3TargetStatement : String
bound3TargetStatement =
  "Use Leray energy with Ladyzhenskaya transport interpolation, diffusion W^{-1,2} control, pressure-gradient W^{-1,2} control, and the NS decomposition to target ||partial_t u_d||_{L2(0,T;W^{-1,2})} <= C(u0,nu)"

bound3RemainingBlockerStatement : String
bound3RemainingBlockerStatement =
  "Current local objects record Ladyzhenskaya, diffusion dual-norm, and pressure-gradient dual-norm as analytic targets only; there is no formal composition proving the L2(0,T;W^{-1,2}) weak time-derivative estimate."

record AubinLionsBound3Receipt : Setω where
  field
    prerequisiteChain :
      Smooth.CarrierNSAubinLionsPrerequisiteChain

    prerequisites :
      List AubinLionsBound3Prerequisite

    prerequisitesAreCanonical :
      prerequisites ≡ canonicalAubinLionsBound3Prerequisites

    lerayEnergyStatus :
      AubinLionsBound3Status

    lerayEnergyStatusIsConsumed :
      lerayEnergyStatus ≡ consumedFromExistingFiniteReceipt

    lerayEnergyBoundRecordedInPrerequisiteChain :
      Smooth.lerayEnergyBoundRecorded prerequisiteChain ≡ true

    ladyzhenskayaStatus :
      AubinLionsBound3Status

    ladyzhenskayaStatusIsTarget :
      ladyzhenskayaStatus ≡ recordedAnalyticTarget

    ladyzhenskayaTargetRecorded :
      Bool

    ladyzhenskayaTargetRecordedIsTrue :
      ladyzhenskayaTargetRecorded ≡ true

    ladyzhenskayaEstimateConstructedHere :
      Bool

    ladyzhenskayaEstimateConstructedHereIsFalse :
      ladyzhenskayaEstimateConstructedHere ≡ false

    diffusionDualNormStatus :
      AubinLionsBound3Status

    diffusionDualNormStatusIsTarget :
      diffusionDualNormStatus ≡ recordedAnalyticTarget

    diffusionDualNormTargetRecorded :
      Bool

    diffusionDualNormTargetRecordedIsTrue :
      diffusionDualNormTargetRecorded ≡ true

    diffusionDualNormEstimateConstructedHere :
      Bool

    diffusionDualNormEstimateConstructedHereIsFalse :
      diffusionDualNormEstimateConstructedHere ≡ false

    pressureGradientStatus :
      AubinLionsBound3Status

    pressureGradientStatusIsTarget :
      pressureGradientStatus ≡ recordedAnalyticTarget

    pressureGradientTargetRecorded :
      Bool

    pressureGradientTargetRecordedIsTrue :
      pressureGradientTargetRecorded ≡ true

    pressureGradientEstimateConstructedHere :
      Bool

    pressureGradientEstimateConstructedHereIsFalse :
      pressureGradientEstimateConstructedHere ≡ false

    nsEquationDecompositionStatus :
      AubinLionsBound3Status

    nsEquationDecompositionStatusIsTarget :
      nsEquationDecompositionStatus ≡ recordedEquationDecompositionTarget

    nsEquationTimeDerivativeTargetRecordedInPrerequisiteChain :
      Smooth.nsEquationTimeDerivativeBoundDerivableTarget prerequisiteChain
      ≡
      true

    bound3EstimateTarget :
      AubinLionsBound3EstimateTarget

    bound3EstimateTargetIsCanonical :
      bound3EstimateTarget ≡ l2TimeWMinusOneTwoDerivativeBoundTarget

    bound3WeakTimeDerivativeTargetRecorded :
      Bool

    bound3WeakTimeDerivativeTargetRecordedIsTrue :
      bound3WeakTimeDerivativeTargetRecorded ≡ true

    fullBound3ProofDerivableFromCurrentLocalObjects :
      Bool

    fullBound3ProofDerivableFromCurrentLocalObjectsIsFalse :
      fullBound3ProofDerivableFromCurrentLocalObjects ≡ false

    compactnessTheoremInstantiatedFromBound3 :
      Bool

    compactnessTheoremInstantiatedFromBound3IsFalse :
      compactnessTheoremInstantiatedFromBound3 ≡ false

    terminalSmoothConvergencePromotedFromBound3 :
      Bool

    terminalSmoothConvergencePromotedFromBound3IsFalse :
      terminalSmoothConvergencePromotedFromBound3 ≡ false

    clayNavierStokesPromotedFromBound3 :
      Bool

    clayNavierStokesPromotedFromBound3IsFalse :
      clayNavierStokesPromotedFromBound3 ≡ false

    remainingBlockers :
      List AubinLionsBound3Blocker

    remainingBlockersAreCanonical :
      remainingBlockers ≡ canonicalAubinLionsBound3Blockers

    targetStatement :
      String

    targetStatementIsCanonical :
      targetStatement ≡ bound3TargetStatement

    remainingBlockerStatement :
      String

    remainingBlockerStatementIsCanonical :
      remainingBlockerStatement ≡ bound3RemainingBlockerStatement

    receiptBoundary :
      List String

open AubinLionsBound3Receipt public

canonicalAubinLionsBound3Receipt :
  AubinLionsBound3Receipt
canonicalAubinLionsBound3Receipt =
  record
    { prerequisiteChain =
        Smooth.canonicalCarrierNSAubinLionsPrerequisiteChain
    ; prerequisites =
        canonicalAubinLionsBound3Prerequisites
    ; prerequisitesAreCanonical =
        refl
    ; lerayEnergyStatus =
        consumedFromExistingFiniteReceipt
    ; lerayEnergyStatusIsConsumed =
        refl
    ; lerayEnergyBoundRecordedInPrerequisiteChain =
        refl
    ; ladyzhenskayaStatus =
        recordedAnalyticTarget
    ; ladyzhenskayaStatusIsTarget =
        refl
    ; ladyzhenskayaTargetRecorded =
        true
    ; ladyzhenskayaTargetRecordedIsTrue =
        refl
    ; ladyzhenskayaEstimateConstructedHere =
        false
    ; ladyzhenskayaEstimateConstructedHereIsFalse =
        refl
    ; diffusionDualNormStatus =
        recordedAnalyticTarget
    ; diffusionDualNormStatusIsTarget =
        refl
    ; diffusionDualNormTargetRecorded =
        true
    ; diffusionDualNormTargetRecordedIsTrue =
        refl
    ; diffusionDualNormEstimateConstructedHere =
        false
    ; diffusionDualNormEstimateConstructedHereIsFalse =
        refl
    ; pressureGradientStatus =
        recordedAnalyticTarget
    ; pressureGradientStatusIsTarget =
        refl
    ; pressureGradientTargetRecorded =
        true
    ; pressureGradientTargetRecordedIsTrue =
        refl
    ; pressureGradientEstimateConstructedHere =
        false
    ; pressureGradientEstimateConstructedHereIsFalse =
        refl
    ; nsEquationDecompositionStatus =
        recordedEquationDecompositionTarget
    ; nsEquationDecompositionStatusIsTarget =
        refl
    ; nsEquationTimeDerivativeTargetRecordedInPrerequisiteChain =
        refl
    ; bound3EstimateTarget =
        l2TimeWMinusOneTwoDerivativeBoundTarget
    ; bound3EstimateTargetIsCanonical =
        refl
    ; bound3WeakTimeDerivativeTargetRecorded =
        true
    ; bound3WeakTimeDerivativeTargetRecordedIsTrue =
        refl
    ; fullBound3ProofDerivableFromCurrentLocalObjects =
        false
    ; fullBound3ProofDerivableFromCurrentLocalObjectsIsFalse =
        refl
    ; compactnessTheoremInstantiatedFromBound3 =
        false
    ; compactnessTheoremInstantiatedFromBound3IsFalse =
        refl
    ; terminalSmoothConvergencePromotedFromBound3 =
        false
    ; terminalSmoothConvergencePromotedFromBound3IsFalse =
        refl
    ; clayNavierStokesPromotedFromBound3 =
        false
    ; clayNavierStokesPromotedFromBound3IsFalse =
        refl
    ; remainingBlockers =
        canonicalAubinLionsBound3Blockers
    ; remainingBlockersAreCanonical =
        refl
    ; targetStatement =
        bound3TargetStatement
    ; targetStatementIsCanonical =
        refl
    ; remainingBlockerStatement =
        bound3RemainingBlockerStatement
    ; remainingBlockerStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Bound3 prerequisite chain is explicit: Leray energy, Ladyzhenskaya, diffusion dual norm, pressure gradient dual norm, and NS decomposition"
        ∷ "Only the Leray input is consumed from an existing finite-depth receipt"
        ∷ "Ladyzhenskaya, diffusion dual-norm, and pressure-gradient controls are recorded targets, not completed local estimates"
        ∷ "The full L2 time W^{-1,2} weak derivative estimate is not derivable from current local objects"
        ∷ "Compactness, terminal smooth convergence, and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

aubinLionsBound3LerayEnergyRecorded :
  lerayEnergyBoundRecordedInPrerequisiteChain canonicalAubinLionsBound3Receipt
  ≡
  refl
aubinLionsBound3LerayEnergyRecorded =
  refl

aubinLionsBound3TargetRecorded :
  bound3WeakTimeDerivativeTargetRecorded canonicalAubinLionsBound3Receipt
  ≡
  true
aubinLionsBound3TargetRecorded =
  refl

aubinLionsBound3FullProofStillBlocked :
  fullBound3ProofDerivableFromCurrentLocalObjects
    canonicalAubinLionsBound3Receipt
  ≡
  false
aubinLionsBound3FullProofStillBlocked =
  refl

aubinLionsBound3CompactnessStillFalse :
  compactnessTheoremInstantiatedFromBound3 canonicalAubinLionsBound3Receipt
  ≡
  false
aubinLionsBound3CompactnessStillFalse =
  refl

aubinLionsBound3ClayStillFalse :
  clayNavierStokesPromotedFromBound3 canonicalAubinLionsBound3Receipt
  ≡
  false
aubinLionsBound3ClayStillFalse =
  refl
