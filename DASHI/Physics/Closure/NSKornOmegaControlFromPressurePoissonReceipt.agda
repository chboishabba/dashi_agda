module DASHI.Physics.Closure.NSKornOmegaControlFromPressurePoissonReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS Korn-level-set h_omega_ctrl route receipt.
--
-- The receipt is fail-closed and self-contained.  It records the exact
-- route stages asked for by the worker lane, together with the canonical
-- blocker that the chain is not closed yet.

data NSKornOmegaControlStage : Set where
  nsSmoothFiniteEnergyHypothesisRecorded :
    NSKornOmegaControlStage

  biaxialBoundaryLambda2ZeroRecorded :
    NSKornOmegaControlStage

  pressurePoissonIdentityRecorded :
    NSKornOmegaControlStage

  biaxialBoundaryTraceS2EqualsTwoLambda3SquaredRecorded :
    NSKornOmegaControlStage

  localCalderonZygmundPressureHessianEstimateRecorded :
    NSKornOmegaControlStage

  nsMomentumCouplingRecorded :
    NSKornOmegaControlStage

  vorticityEquationRecorded :
    NSKornOmegaControlStage

  vorticityStrainProductionRecorded :
    NSKornOmegaControlStage

  targetHOmegaCtrlEstimateRecorded :
    NSKornOmegaControlStage

  chainNotClosedRecorded :
    NSKornOmegaControlStage

canonicalNSKornOmegaControlStages :
  List NSKornOmegaControlStage
canonicalNSKornOmegaControlStages =
  nsSmoothFiniteEnergyHypothesisRecorded
  ∷ biaxialBoundaryLambda2ZeroRecorded
  ∷ pressurePoissonIdentityRecorded
  ∷ biaxialBoundaryTraceS2EqualsTwoLambda3SquaredRecorded
  ∷ localCalderonZygmundPressureHessianEstimateRecorded
  ∷ nsMomentumCouplingRecorded
  ∷ vorticityEquationRecorded
  ∷ vorticityStrainProductionRecorded
  ∷ targetHOmegaCtrlEstimateRecorded
  ∷ chainNotClosedRecorded
  ∷ []

data NSKornOmegaControlBlocker : Set where
  chainNotClosedBlocker :
    NSKornOmegaControlBlocker

canonicalNSKornOmegaControlBlockers :
  List NSKornOmegaControlBlocker
canonicalNSKornOmegaControlBlockers =
  chainNotClosedBlocker
  ∷ []

canonicalNSSmoothFiniteEnergyHypothesisStatement :
  String
canonicalNSSmoothFiniteEnergyHypothesisStatement =
  "NS smooth finite-energy hypothesis recorded for the Korn-level-set h_omega_ctrl route."

canonicalBiaxialBoundaryLambda2ZeroStatement :
  String
canonicalBiaxialBoundaryLambda2ZeroStatement =
  "Biaxial boundary hypothesis recorded with lambda2 = 0."

canonicalPressurePoissonIdentityStatement :
  String
canonicalPressurePoissonIdentityStatement =
  "-Delta p = tr(S^2) - |omega|^2/4."

canonicalBiaxialBoundaryTraceS2Statement :
  String
canonicalBiaxialBoundaryTraceS2Statement =
  "On the biaxial boundary, tr(S^2) = 2 lambda3^2."

canonicalLocalCalderonZygmundStatement :
  String
canonicalLocalCalderonZygmundStatement =
  "Local Calderon-Zygmund pressure-Hessian estimate recorded as the pressure-to-Hessian control step."

canonicalNSMomentumCouplingStatement :
  String
canonicalNSMomentumCouplingStatement =
  "NS momentum coupling recorded as the next route stage."

canonicalVorticityEquationStatement :
  String
canonicalVorticityEquationStatement =
  "Vorticity equation recorded as the carrier for the h_omega_ctrl route."

canonicalVorticityStrainProductionStatement :
  String
canonicalVorticityStrainProductionStatement =
  "Vorticity-strain production S omega is recorded explicitly."

canonicalHOmegaCtrlTargetStatement :
  String
canonicalHOmegaCtrlTargetStatement =
  "Target estimate: h_omega_ctrl ||omega||_L4(layer) <= C_omega ||S||_L4(layer)."

canonicalChainNotClosedStatement :
  String
canonicalChainNotClosedStatement =
  "Explicit blocker: the route chain is not closed."

canonicalNSKornOmegaControlReceiptBoundary :
  List String
canonicalNSKornOmegaControlReceiptBoundary =
  canonicalNSSmoothFiniteEnergyHypothesisStatement
  ∷ canonicalBiaxialBoundaryLambda2ZeroStatement
  ∷ canonicalPressurePoissonIdentityStatement
  ∷ canonicalBiaxialBoundaryTraceS2Statement
  ∷ canonicalLocalCalderonZygmundStatement
  ∷ canonicalNSMomentumCouplingStatement
  ∷ canonicalVorticityEquationStatement
  ∷ canonicalVorticityStrainProductionStatement
  ∷ canonicalHOmegaCtrlTargetStatement
  ∷ canonicalChainNotClosedStatement
  ∷ []

data NSKornOmegaControlPromotion : Set where

nsKornOmegaControlPromotionImpossibleHere :
  NSKornOmegaControlPromotion →
  ⊥
nsKornOmegaControlPromotionImpossibleHere ()

record NSKornOmegaControlFromPressurePoissonReceipt : Setω where
  field
    stages :
      List NSKornOmegaControlStage

    stagesAreCanonical :
      stages ≡ canonicalNSKornOmegaControlStages

    smoothFiniteEnergyHypothesisStage :
      NSKornOmegaControlStage

    smoothFiniteEnergyHypothesisStageIsCanonical :
      smoothFiniteEnergyHypothesisStage
      ≡ nsSmoothFiniteEnergyHypothesisRecorded

    biaxialBoundaryLambda2ZeroStage :
      NSKornOmegaControlStage

    biaxialBoundaryLambda2ZeroStageIsCanonical :
      biaxialBoundaryLambda2ZeroStage
      ≡ biaxialBoundaryLambda2ZeroRecorded

    pressurePoissonIdentityStage :
      NSKornOmegaControlStage

    pressurePoissonIdentityStageIsCanonical :
      pressurePoissonIdentityStage
      ≡ pressurePoissonIdentityRecorded

    biaxialBoundaryTraceS2EqualsTwoLambda3SquaredStage :
      NSKornOmegaControlStage

    biaxialBoundaryTraceS2EqualsTwoLambda3SquaredStageIsCanonical :
      biaxialBoundaryTraceS2EqualsTwoLambda3SquaredStage
      ≡ biaxialBoundaryTraceS2EqualsTwoLambda3SquaredRecorded

    localCalderonZygmundPressureHessianEstimateStage :
      NSKornOmegaControlStage

    localCalderonZygmundPressureHessianEstimateStageIsCanonical :
      localCalderonZygmundPressureHessianEstimateStage
      ≡ localCalderonZygmundPressureHessianEstimateRecorded

    nsMomentumCouplingStage :
      NSKornOmegaControlStage

    nsMomentumCouplingStageIsCanonical :
      nsMomentumCouplingStage ≡ nsMomentumCouplingRecorded

    vorticityEquationStage :
      NSKornOmegaControlStage

    vorticityEquationStageIsCanonical :
      vorticityEquationStage ≡ vorticityEquationRecorded

    vorticityStrainProductionStage :
      NSKornOmegaControlStage

    vorticityStrainProductionStageIsCanonical :
      vorticityStrainProductionStage ≡ vorticityStrainProductionRecorded

    targetHOmegaCtrlEstimateStage :
      NSKornOmegaControlStage

    targetHOmegaCtrlEstimateStageIsCanonical :
      targetHOmegaCtrlEstimateStage ≡ targetHOmegaCtrlEstimateRecorded

    blocker :
      NSKornOmegaControlBlocker

    blockerIsCanonical :
      blocker ≡ chainNotClosedBlocker

    chainNotClosed :
      Bool

    chainNotClosedIsTrue :
      chainNotClosed ≡ true

    promotion :
      Bool

    promotionIsFalse :
      promotion ≡ false

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalNSKornOmegaControlReceiptBoundary

    summary :
      String

    summaryIsCanonical :
      summary ≡ canonicalHOmegaCtrlTargetStatement

open NSKornOmegaControlFromPressurePoissonReceipt public

canonicalNSKornOmegaControlFromPressurePoissonReceipt :
  NSKornOmegaControlFromPressurePoissonReceipt
canonicalNSKornOmegaControlFromPressurePoissonReceipt =
  record
    { stages =
        canonicalNSKornOmegaControlStages
    ; stagesAreCanonical =
        refl
    ; smoothFiniteEnergyHypothesisStage =
        nsSmoothFiniteEnergyHypothesisRecorded
    ; smoothFiniteEnergyHypothesisStageIsCanonical =
        refl
    ; biaxialBoundaryLambda2ZeroStage =
        biaxialBoundaryLambda2ZeroRecorded
    ; biaxialBoundaryLambda2ZeroStageIsCanonical =
        refl
    ; pressurePoissonIdentityStage =
        pressurePoissonIdentityRecorded
    ; pressurePoissonIdentityStageIsCanonical =
        refl
    ; biaxialBoundaryTraceS2EqualsTwoLambda3SquaredStage =
        biaxialBoundaryTraceS2EqualsTwoLambda3SquaredRecorded
    ; biaxialBoundaryTraceS2EqualsTwoLambda3SquaredStageIsCanonical =
        refl
    ; localCalderonZygmundPressureHessianEstimateStage =
        localCalderonZygmundPressureHessianEstimateRecorded
    ; localCalderonZygmundPressureHessianEstimateStageIsCanonical =
        refl
    ; nsMomentumCouplingStage =
        nsMomentumCouplingRecorded
    ; nsMomentumCouplingStageIsCanonical =
        refl
    ; vorticityEquationStage =
        vorticityEquationRecorded
    ; vorticityEquationStageIsCanonical =
        refl
    ; vorticityStrainProductionStage =
        vorticityStrainProductionRecorded
    ; vorticityStrainProductionStageIsCanonical =
        refl
    ; targetHOmegaCtrlEstimateStage =
        targetHOmegaCtrlEstimateRecorded
    ; targetHOmegaCtrlEstimateStageIsCanonical =
        refl
    ; blocker =
        chainNotClosedBlocker
    ; blockerIsCanonical =
        refl
    ; chainNotClosed =
        true
    ; chainNotClosedIsTrue =
        refl
    ; promotion =
        false
    ; promotionIsFalse =
        refl
    ; receiptBoundary =
        canonicalNSKornOmegaControlReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    ; summary =
        canonicalHOmegaCtrlTargetStatement
    ; summaryIsCanonical =
        refl
    }

canonicalReceipt :
  NSKornOmegaControlFromPressurePoissonReceipt
canonicalReceipt =
  canonicalNSKornOmegaControlFromPressurePoissonReceipt

canonicalReceiptStages :
  stages canonicalReceipt ≡ canonicalNSKornOmegaControlStages
canonicalReceiptStages =
  stagesAreCanonical canonicalReceipt

canonicalReceiptPromotionIsFalse :
  promotion canonicalReceipt ≡ false
canonicalReceiptPromotionIsFalse =
  promotionIsFalse canonicalReceipt

canonicalReceiptChainIsNotClosed :
  chainNotClosed canonicalReceipt ≡ true
canonicalReceiptChainIsNotClosed =
  chainNotClosedIsTrue canonicalReceipt

canonicalReceiptBlockerIsCanonical :
  blocker canonicalReceipt ≡ chainNotClosedBlocker
canonicalReceiptBlockerIsCanonical =
  blockerIsCanonical canonicalReceipt

canonicalReceiptBoundaryIsCanonical :
  receiptBoundary canonicalReceipt ≡ canonicalNSKornOmegaControlReceiptBoundary
canonicalReceiptBoundaryIsCanonical =
  receiptBoundaryIsCanonical canonicalReceipt

canonicalReceiptSummaryIsCanonical :
  summary canonicalReceipt ≡ canonicalHOmegaCtrlTargetStatement
canonicalReceiptSummaryIsCanonical =
  summaryIsCanonical canonicalReceipt
