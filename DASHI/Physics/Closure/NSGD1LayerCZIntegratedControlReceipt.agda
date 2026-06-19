module DASHI.Physics.Closure.NSGD1LayerCZIntegratedControlReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- GD1 CZ/trace constants surface.
--
-- This is a fail-closed receipt surface for GD1 LayerCZ constants.
-- It records the corrected admissible formulation:
--   * no pointwise/Linf CZ bound is taken as a discharge gate;
--   * pressure Hessian control is recorded via integrated/Lp quantities;
--   * boundary trace control is routed through Sobolev + coarea;
--   * alpha = 1 - 2 CCZ is an explicit positivity assumption/condition;
--   * a pointwise constant CZ claim is explicitly rejected.
--
-- All final discharge and promotion flags remain false unless separate local
-- evidence sets them to true (none are imported or assumed here).

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSGD1LayerCZIntegratedControlStatus : Set where
  gd1LayerCZIntegratedControlReceiptRecorded :
    NSGD1LayerCZIntegratedControlStatus

data NSGD1LayerCZIntegratedControlStage : Set where
  noLinfCZBoundRejected :
    NSGD1LayerCZIntegratedControlStage
  pressureHessianIntegratedLpControlRecorded :
    NSGD1LayerCZIntegratedControlStage
  traceSobolevControlRecorded :
    NSGD1LayerCZIntegratedControlStage
  coareaControlRecorded :
    NSGD1LayerCZIntegratedControlStage
  alphaPositivityAssumptionRecorded :
    NSGD1LayerCZIntegratedControlStage
  pointwiseConstantClaimRejected :
    NSGD1LayerCZIntegratedControlStage
  failClosedFinalDischargeFalseRecorded :
    NSGD1LayerCZIntegratedControlStage

canonicalNSGD1LayerCZIntegratedControlStages :
  List NSGD1LayerCZIntegratedControlStage
canonicalNSGD1LayerCZIntegratedControlStages =
  noLinfCZBoundRejected
  ∷ pressureHessianIntegratedLpControlRecorded
  ∷ traceSobolevControlRecorded
  ∷ coareaControlRecorded
  ∷ alphaPositivityAssumptionRecorded
  ∷ pointwiseConstantClaimRejected
  ∷ failClosedFinalDischargeFalseRecorded
  ∷ []

data NSGD1LayerCZIntegratedControlBlocker : Set where
  lInfCZBoundNotDischarged :
    NSGD1LayerCZIntegratedControlBlocker
  pressureHessianLpGateOpen :
    NSGD1LayerCZIntegratedControlBlocker
  traceSobolevCoareaGateOpen :
    NSGD1LayerCZIntegratedControlBlocker
  alphaPositivityStillAssumptionOnly :
    NSGD1LayerCZIntegratedControlBlocker
  pointwiseConstantClaimRejectedAsOpenGate :
    NSGD1LayerCZIntegratedControlBlocker
  dischargeFinalStillOpen :
    NSGD1LayerCZIntegratedControlBlocker

canonicalNSGD1LayerCZIntegratedControlBlockers :
  List NSGD1LayerCZIntegratedControlBlocker
canonicalNSGD1LayerCZIntegratedControlBlockers =
  lInfCZBoundNotDischarged
  ∷ pressureHessianLpGateOpen
  ∷ traceSobolevCoareaGateOpen
  ∷ alphaPositivityStillAssumptionOnly
  ∷ pointwiseConstantClaimRejectedAsOpenGate
  ∷ dischargeFinalStillOpen
  ∷ []

-- Exact named gates / named conditions captured on this surface.

pressureHessianLpIntegratedGateText : String
pressureHessianLpIntegratedGateText =
  "pressure-hessian-integrated-control-gate"

traceSobolevCoareaGateText : String
traceSobolevCoareaGateText =
  "surface-trace-sobolev-coarea-control-gate"

alphaPositivityGateText : String
alphaPositivityGateText =
  "alpha=1-2*CCZ-positivity-assumption"

pointwiseConstantRejectionText : String
pointwiseConstantRejectionText =
  "reject-pointwise-CZ-constant-claim"

linfCZGateRejectionText : String
linfCZGateRejectionText =
  "reject-pointwise-Linf-CZ-bound-as-discharge-gate"

stageSummaryText : String
stageSummaryText =
  "GD1 LayerCZ/CZ-trace constants surface is recorded with integrated/Lp pressure-Hessian control, boundary Sobolev+coarea trace control, and alpha=1-2*CCZ positivity as explicit assumptions; the pointwise Linf/CZ constant claim is rejected."

dependencyNames : List String
dependencyNames =
  "pressure-hessian-integrated-control-gate"
  ∷ "surface-trace-sobolev-coarea-control-gate"
  ∷ "alpha=1-2*CCZ-positivity-assumption"
  ∷ "reject-pointwise-CZ-constant-claim"
  ∷ "reject-pointwise-Linf-CZ-bound-as-discharge-gate"
  ∷ []

record NSGD1LayerCZIntegratedControlReceipt : Setω where
  field
    status :
      NSGD1LayerCZIntegratedControlStatus
    statusIsCanonical :
      status ≡ gd1LayerCZIntegratedControlReceiptRecorded

    stageTrail :
      List NSGD1LayerCZIntegratedControlStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSGD1LayerCZIntegratedControlStages

    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSGD1LayerCZIntegratedControlStages

    blockerTrail :
      List NSGD1LayerCZIntegratedControlBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSGD1LayerCZIntegratedControlBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡
      listLength canonicalNSGD1LayerCZIntegratedControlBlockers

    pressureHessianLpIntegratedGate :
      Bool
    pressureHessianLpIntegratedGateIsTrue :
      pressureHessianLpIntegratedGate ≡ true

    traceSobolevCoareaGate :
      Bool
    traceSobolevCoareaGateIsTrue :
      traceSobolevCoareaGate ≡ true

    alphaPositivityGate :
      Bool
    alphaPositivityGateIsTrue :
      alphaPositivityGate ≡ true

    pointwiseConstantClaimRejectedGate :
      Bool
    pointwiseConstantClaimRejectedGateIsTrue :
      pointwiseConstantClaimRejectedGate ≡ true

    lInfCZPointwiseBoundRejected :
      Bool
    lInfCZPointwiseBoundRejectedIsTrue :
      lInfCZPointwiseBoundRejected ≡ true

    pressureHessianLpIntegratedGateName :
      String
    pressureHessianLpIntegratedGateNameIsCanonical :
      pressureHessianLpIntegratedGateName
        ≡ pressureHessianLpIntegratedGateText

    traceSobolevCoareaGateName :
      String
    traceSobolevCoareaGateNameIsCanonical :
      traceSobolevCoareaGateName ≡ traceSobolevCoareaGateText

    alphaPositivityGateName :
      String
    alphaPositivityGateNameIsCanonical :
      alphaPositivityGateName ≡ alphaPositivityGateText

    pointwiseConstantRejectionGateName :
      String
    pointwiseConstantRejectionGateNameIsCanonical :
      pointwiseConstantRejectionGateName ≡ pointwiseConstantRejectionText

    lInfCZGateRejectionGateName :
      String
    lInfCZGateRejectionGateNameIsCanonical :
      lInfCZGateRejectionGateName ≡ linfCZGateRejectionText

    dependencyRows :
      List String
    dependencyRowsIsCanonical :
      dependencyRows ≡ dependencyNames

    dependencyRowCount :
      Nat
    dependencyRowCountIsCanonical :
      dependencyRowCount ≡ listLength dependencyNames

    stageSummary :
      String
    stageSummaryIsCanonical :
      stageSummary ≡ stageSummaryText

    finalDischarge :
      Bool
    finalDischargeIsFalse :
      finalDischarge ≡ false

    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    gD1LayerCZFinalRoutePromoted :
      Bool
    gD1LayerCZFinalRoutePromotedIsFalse :
      gD1LayerCZFinalRoutePromoted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡
      ("No Linf CZ bound is recorded as an admissible discharge gate."
      ∷ "Pressure Hessian control appears as integrated/Lp gate and not pointwise."
      ∷ "Surface trace control is routed through Sobolev+coarea, not uniform constants."
      ∷ "The explicit positivity condition alpha = 1 - 2 CCZ is required."
      ∷ "A pointwise constant CZ claim is explicitly rejected on this surface."
      ∷ "All final discharge and Clay promotion rows remain false."
      ∷ [])

data NSGD1LayerCZIntegratedControlPromotion : Set where

nsGD1LayerCZIntegratedControlPromotionImpossibleHere :
  NSGD1LayerCZIntegratedControlPromotion → ⊥
nsGD1LayerCZIntegratedControlPromotionImpossibleHere ()

canonicalNSGD1LayerCZIntegratedControlReceipt :
  NSGD1LayerCZIntegratedControlReceipt
canonicalNSGD1LayerCZIntegratedControlReceipt =
  record
    { status =
        gd1LayerCZIntegratedControlReceiptRecorded
    ; statusIsCanonical =
        refl
    ; stageTrail =
        canonicalNSGD1LayerCZIntegratedControlStages
    ; stageTrailIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSGD1LayerCZIntegratedControlStages
    ; stageCountIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSGD1LayerCZIntegratedControlBlockers
    ; blockerTrailIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSGD1LayerCZIntegratedControlBlockers
    ; blockerCountIsCanonical =
        refl
    ; pressureHessianLpIntegratedGate =
        true
    ; pressureHessianLpIntegratedGateIsTrue =
        refl
    ; traceSobolevCoareaGate =
        true
    ; traceSobolevCoareaGateIsTrue =
        refl
    ; alphaPositivityGate =
        true
    ; alphaPositivityGateIsTrue =
        refl
    ; pointwiseConstantClaimRejectedGate =
        true
    ; pointwiseConstantClaimRejectedGateIsTrue =
        refl
    ; lInfCZPointwiseBoundRejected =
        true
    ; lInfCZPointwiseBoundRejectedIsTrue =
        refl
    ; pressureHessianLpIntegratedGateName =
        pressureHessianLpIntegratedGateText
    ; pressureHessianLpIntegratedGateNameIsCanonical =
        refl
    ; traceSobolevCoareaGateName =
        traceSobolevCoareaGateText
    ; traceSobolevCoareaGateNameIsCanonical =
        refl
    ; alphaPositivityGateName =
        alphaPositivityGateText
    ; alphaPositivityGateNameIsCanonical =
        refl
    ; pointwiseConstantRejectionGateName =
        pointwiseConstantRejectionText
    ; pointwiseConstantRejectionGateNameIsCanonical =
        refl
    ; lInfCZGateRejectionGateName =
        linfCZGateRejectionText
    ; lInfCZGateRejectionGateNameIsCanonical =
        refl
    ; dependencyRows =
        dependencyNames
    ; dependencyRowsIsCanonical =
        refl
    ; dependencyRowCount =
        listLength dependencyNames
    ; dependencyRowCountIsCanonical =
        refl
    ; stageSummary =
        stageSummaryText
    ; stageSummaryIsCanonical =
        refl
    ; finalDischarge =
        false
    ; finalDischargeIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; gD1LayerCZFinalRoutePromoted =
        false
    ; gD1LayerCZFinalRoutePromotedIsFalse =
        refl
    ; receiptBoundary =
        "No Linf CZ bound is recorded as an admissible discharge gate."
        ∷ "Pressure Hessian control appears as integrated/Lp gate and not pointwise."
        ∷ "Surface trace control is routed through Sobolev+coarea, not uniform constants."
        ∷ "The explicit positivity condition alpha = 1 - 2 CCZ is required."
        ∷ "A pointwise constant CZ claim is explicitly rejected on this surface."
        ∷ "All final discharge and Clay promotion rows remain false."
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    }

canonicalNSGD1LayerCZIntegratedControlNoDischarge :
  clayNavierStokesPromoted canonicalNSGD1LayerCZIntegratedControlReceipt ≡ false
canonicalNSGD1LayerCZIntegratedControlNoDischarge =
  refl
