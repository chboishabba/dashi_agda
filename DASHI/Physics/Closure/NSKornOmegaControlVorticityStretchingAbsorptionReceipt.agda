module DASHI.Physics.Closure.NSKornOmegaControlVorticityStretchingAbsorptionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- h_omega_ctrl vorticity-stretching absorption receipt.
--
-- This file is a self-contained analytic receipt, not a proof of the
-- absorption estimate.  It records the control surface for the omega
-- equation, the symmetric strain source term, skew-part cancellation,
-- the L4 layer estimate, pressure/CZ feed-in, and the target absorption
-- shape
--
--   ||omega||_L4 <= C ||S||_L4.
--
-- The exact circularity blocker is also recorded: if S depends on omega,
-- then the estimate becomes circular and promotion stays fail-closed.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Receipt status.

data HOmegaCtrlReceiptStatus : Set where
  hOmegaCtrlVorticityStretchingAbsorptionRecorded :
    HOmegaCtrlReceiptStatus

------------------------------------------------------------------------
-- Canonical stages.

data HOmegaCtrlVorticityAbsorptionStage : Set where
  recordVorticityEquation :
    HOmegaCtrlVorticityAbsorptionStage

  recordSOmegaProduction :
    HOmegaCtrlVorticityAbsorptionStage

  recordSkewPartCancellation :
    HOmegaCtrlVorticityAbsorptionStage

  recordL4LayerEstimate :
    HOmegaCtrlVorticityAbsorptionStage

  recordPressureCZFeedIn :
    HOmegaCtrlVorticityAbsorptionStage

  recordAbsorptionTarget :
    HOmegaCtrlVorticityAbsorptionStage

  recordExactCircularityBlocker :
    HOmegaCtrlVorticityAbsorptionStage

  recordFailClosedPromotion :
    HOmegaCtrlVorticityAbsorptionStage

canonicalVorticityAbsorptionStages :
  List HOmegaCtrlVorticityAbsorptionStage
canonicalVorticityAbsorptionStages =
  recordVorticityEquation
  ∷ recordSOmegaProduction
  ∷ recordSkewPartCancellation
  ∷ recordL4LayerEstimate
  ∷ recordPressureCZFeedIn
  ∷ recordAbsorptionTarget
  ∷ recordExactCircularityBlocker
  ∷ recordFailClosedPromotion
  ∷ []

canonicalVorticityAbsorptionStageCount : Nat
canonicalVorticityAbsorptionStageCount =
  listLength canonicalVorticityAbsorptionStages

canonicalVorticityAbsorptionStageCountIs8 :
  canonicalVorticityAbsorptionStageCount ≡ 8
canonicalVorticityAbsorptionStageCountIs8 =
  refl

vorticityEquationStatement : String
vorticityEquationStatement =
  "Vorticity equation recorded: transport plus stretching decomposition for omega, with the strain source isolated as the h_omega_ctrl control input."

sOmegaProductionStatement : String
sOmegaProductionStatement =
  "S omega production recorded: the symmetric strain S is the production operator feeding the omega stretching term."

skewPartCancellationStatement : String
skewPartCancellationStatement =
  "Skew-part cancellation recorded: the antisymmetric part of grad u cancels from the stretching pairing, leaving only the symmetric strain contribution."

l4LayerEstimateStatement : String
l4LayerEstimateStatement =
  "L4 layer estimate recorded: the absorption route is measured on the layerwise L4 control surface used by h_omega_ctrl."

pressureCZFeedInStatement : String
pressureCZFeedInStatement =
  "Pressure/CZ feed-in recorded: pressure terms are routed through Calderon-Zygmund control as lower-order feed-in, not as a direct absorber."

absorptionTargetStatement : String
absorptionTargetStatement =
  "Target absorption recorded: ||omega||_L4 <= C ||S||_L4, with C treated as the fixed control constant of this receipt."

exactCircularityBlockerStatement : String
exactCircularityBlockerStatement =
  "Exact circularity blocker recorded: if S depends on omega, the target becomes circular and cannot be promoted from this surface."

failClosedPromotionStatement : String
failClosedPromotionStatement =
  "Fail-closed promotion recorded: no absorption theorem is promoted here."

------------------------------------------------------------------------
-- Canonical blockers.

data HOmegaCtrlVorticityAbsorptionBlocker : Set where
  exactCircularityIfSDependsOnOmega :
    HOmegaCtrlVorticityAbsorptionBlocker

  pressureCZFeedInNeedsIndependentSControl :
    HOmegaCtrlVorticityAbsorptionBlocker

  l4LayerEstimateDoesNotCloseWithoutExternalStrain :
    HOmegaCtrlVorticityAbsorptionBlocker

  promotionRemainsFailClosed :
    HOmegaCtrlVorticityAbsorptionBlocker

canonicalVorticityAbsorptionBlockers :
  List HOmegaCtrlVorticityAbsorptionBlocker
canonicalVorticityAbsorptionBlockers =
  exactCircularityIfSDependsOnOmega
  ∷ pressureCZFeedInNeedsIndependentSControl
  ∷ l4LayerEstimateDoesNotCloseWithoutExternalStrain
  ∷ promotionRemainsFailClosed
  ∷ []

canonicalVorticityAbsorptionBlockerCount : Nat
canonicalVorticityAbsorptionBlockerCount =
  listLength canonicalVorticityAbsorptionBlockers

canonicalVorticityAbsorptionBlockerCountIs4 :
  canonicalVorticityAbsorptionBlockerCount ≡ 4
canonicalVorticityAbsorptionBlockerCountIs4 =
  refl

blockerStatement :
  HOmegaCtrlVorticityAbsorptionBlocker →
  String
blockerStatement exactCircularityIfSDependsOnOmega =
  exactCircularityBlockerStatement
blockerStatement pressureCZFeedInNeedsIndependentSControl =
  "Pressure/CZ feed-in blocker: the Calderon-Zygmund contribution can support the ledger only if S is controlled independently of omega."
blockerStatement l4LayerEstimateDoesNotCloseWithoutExternalStrain =
  "L4 blocker: the layer estimate does not close without an external strain bound that is not itself defined from omega."
blockerStatement promotionRemainsFailClosed =
  failClosedPromotionStatement

------------------------------------------------------------------------
-- Promotion surface.

data HOmegaCtrlAbsorptionPromotion : Set where

promotionImpossibleHere :
  HOmegaCtrlAbsorptionPromotion →
  ⊥
promotionImpossibleHere ()

canonicalVorticityAbsorptionSummary : String
canonicalVorticityAbsorptionSummary =
  "h_omega_ctrl receipt: vorticity equation, S omega production, skew-part cancellation, L4 layer estimate, pressure/CZ feed-in, target absorption ||omega||_L4 <= C ||S||_L4, exact circularity blocker when S depends on omega, and fail-closed promotion false."

------------------------------------------------------------------------
-- Main receipt record.

record NSKornOmegaControlVorticityStretchingAbsorptionReceipt : Setω where
  field
    status :
      HOmegaCtrlReceiptStatus

    statusIsCanonical :
      status ≡ hOmegaCtrlVorticityStretchingAbsorptionRecorded

    stages :
      List HOmegaCtrlVorticityAbsorptionStage

    stagesAreCanonical :
      stages ≡ canonicalVorticityAbsorptionStages

    stageCount :
      Nat

    stageCountIsCanonical :
      stageCount ≡ canonicalVorticityAbsorptionStageCount

    stageCountIs8 :
      stageCount ≡ 8

    blockers :
      List HOmegaCtrlVorticityAbsorptionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVorticityAbsorptionBlockers

    blockerCount :
      Nat

    blockerCountIsCanonical :
      blockerCount ≡ canonicalVorticityAbsorptionBlockerCount

    blockerCountIs4 :
      blockerCount ≡ 4

    vorticityEquation :
      String

    vorticityEquationIsCanonical :
      vorticityEquation ≡ vorticityEquationStatement

    sOmegaProduction :
      String

    sOmegaProductionIsCanonical :
      sOmegaProduction ≡ sOmegaProductionStatement

    skewPartCancellation :
      String

    skewPartCancellationIsCanonical :
      skewPartCancellation ≡ skewPartCancellationStatement

    l4LayerEstimate :
      String

    l4LayerEstimateIsCanonical :
      l4LayerEstimate ≡ l4LayerEstimateStatement

    pressureCZFeedIn :
      String

    pressureCZFeedInIsCanonical :
      pressureCZFeedIn ≡ pressureCZFeedInStatement

    absorptionTarget :
      String

    absorptionTargetIsCanonical :
      absorptionTarget ≡ absorptionTargetStatement

    exactCircularityBlocker :
      String

    exactCircularityBlockerIsCanonical :
      exactCircularityBlocker ≡ exactCircularityBlockerStatement

    circularityBlockerActive :
      Bool

    circularityBlockerActiveIsTrue :
      circularityBlockerActive ≡ true

    promotionRecorded :
      Bool

    promotionRecordedIsFalse :
      promotionRecorded ≡ false

    summary :
      String

    summaryIsCanonical :
      summary ≡ canonicalVorticityAbsorptionSummary

    promotionFlags :
      List HOmegaCtrlAbsorptionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSKornOmegaControlVorticityStretchingAbsorptionReceipt public

canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt :
  NSKornOmegaControlVorticityStretchingAbsorptionReceipt
canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt =
  record
    { status =
        hOmegaCtrlVorticityStretchingAbsorptionRecorded
    ; statusIsCanonical =
        refl
    ; stages =
        canonicalVorticityAbsorptionStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        canonicalVorticityAbsorptionStageCount
    ; stageCountIsCanonical =
        refl
    ; stageCountIs8 =
        canonicalVorticityAbsorptionStageCountIs8
    ; blockers =
        canonicalVorticityAbsorptionBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        canonicalVorticityAbsorptionBlockerCount
    ; blockerCountIsCanonical =
        refl
    ; blockerCountIs4 =
        canonicalVorticityAbsorptionBlockerCountIs4
    ; vorticityEquation =
        vorticityEquationStatement
    ; vorticityEquationIsCanonical =
        refl
    ; sOmegaProduction =
        sOmegaProductionStatement
    ; sOmegaProductionIsCanonical =
        refl
    ; skewPartCancellation =
        skewPartCancellationStatement
    ; skewPartCancellationIsCanonical =
        refl
    ; l4LayerEstimate =
        l4LayerEstimateStatement
    ; l4LayerEstimateIsCanonical =
        refl
    ; pressureCZFeedIn =
        pressureCZFeedInStatement
    ; pressureCZFeedInIsCanonical =
        refl
    ; absorptionTarget =
        absorptionTargetStatement
    ; absorptionTargetIsCanonical =
        refl
    ; exactCircularityBlocker =
        exactCircularityBlockerStatement
    ; exactCircularityBlockerIsCanonical =
        refl
    ; circularityBlockerActive =
        true
    ; circularityBlockerActiveIsTrue =
        refl
    ; promotionRecorded =
        false
    ; promotionRecordedIsFalse =
        refl
    ; summary =
        canonicalVorticityAbsorptionSummary
    ; summaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Stage ledger: vorticity equation, S omega production, skew cancellation, L4 layer estimate, pressure/CZ feed-in, target absorption, circularity blocker, and fail-closed promotion"
        ∷ "Canonical stage count is 8 and canonical blocker count is 4"
        ∷ "Exact circularity blocker: if S depends on omega, the absorption claim is circular"
        ∷ "Pressure/CZ feed-in is recorded only as lower-order support, not as a closure proof"
        ∷ "The receipt records ||omega||_L4 <= C ||S||_L4 as the target shape only"
        ∷ "Promotion remains false on this surface"
        ∷ []
    }

------------------------------------------------------------------------
-- Canonical projections.

canonicalReceiptStatus :
  HOmegaCtrlReceiptStatus
canonicalReceiptStatus =
  status canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt

canonicalReceiptStatusIsCanonical :
  canonicalReceiptStatus ≡
  hOmegaCtrlVorticityStretchingAbsorptionRecorded
canonicalReceiptStatusIsCanonical =
  refl

canonicalReceiptStages :
  List HOmegaCtrlVorticityAbsorptionStage
canonicalReceiptStages =
  stages canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt

canonicalReceiptStagesAreCanonical :
  canonicalReceiptStages ≡ canonicalVorticityAbsorptionStages
canonicalReceiptStagesAreCanonical =
  refl

canonicalReceiptStageCount :
  Nat
canonicalReceiptStageCount =
  stageCount canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt

canonicalReceiptStageCountIs8 :
  canonicalReceiptStageCount ≡ 8
canonicalReceiptStageCountIs8 =
  refl

canonicalReceiptBlockers :
  List HOmegaCtrlVorticityAbsorptionBlocker
canonicalReceiptBlockers =
  blockers canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt

canonicalReceiptBlockersAreCanonical :
  canonicalReceiptBlockers ≡ canonicalVorticityAbsorptionBlockers
canonicalReceiptBlockersAreCanonical =
  refl

canonicalReceiptBlockerCount :
  Nat
canonicalReceiptBlockerCount =
  blockerCount canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt

canonicalReceiptBlockerCountIs4 :
  canonicalReceiptBlockerCount ≡ 4
canonicalReceiptBlockerCountIs4 =
  refl

canonicalReceiptPromotionRecorded :
  Bool
canonicalReceiptPromotionRecorded =
  promotionRecorded canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt

canonicalReceiptPromotionRecordedIsFalse :
  canonicalReceiptPromotionRecorded ≡ false
canonicalReceiptPromotionRecordedIsFalse =
  refl

canonicalReceiptCircularityBlocked :
  Bool
canonicalReceiptCircularityBlocked =
  circularityBlockerActive canonicalNSKornOmegaControlVorticityStretchingAbsorptionReceipt

canonicalReceiptCircularityBlockedIsTrue :
  canonicalReceiptCircularityBlocked ≡ true
canonicalReceiptCircularityBlockedIsTrue =
  refl

canonicalReceiptNoPromotion :
  HOmegaCtrlAbsorptionPromotion →
  ⊥
canonicalReceiptNoPromotion =
  promotionImpossibleHere
