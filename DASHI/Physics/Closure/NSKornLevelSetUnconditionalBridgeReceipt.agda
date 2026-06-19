module DASHI.Physics.Closure.NSKornLevelSetUnconditionalBridgeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NSKornLevelSet unconditional bridge receipt.
--
-- This receipt is self-contained and fail-closed.  It mirrors the existing
-- Korn/omega-control route conceptually: the conditional KornLevelSet packet
-- is recorded as available under h_omega_ctrl, the required implication
-- h_omega_ctrl_from_NS is recorded explicitly, and the exact gateway for
-- flipping unconditional promotion is named but not opened.  Unconditional
-- promotion stays false here.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSKornLevelSetBridgeRow : Set where
  conditionalKornLevelSetAvailableUnderHOmegaCtrlRow :
    NSKornLevelSetBridgeRow
  hOmegaCtrlFromNSRecordedRow :
    NSKornLevelSetBridgeRow
  unconditionalPromotionGatewayRecordedRow :
    NSKornLevelSetBridgeRow
  unconditionalPromotionRemainsFalseRow :
    NSKornLevelSetBridgeRow
  clayPromotionRemainsFalseRow :
    NSKornLevelSetBridgeRow

canonicalNSKornLevelSetBridgeRows :
  List NSKornLevelSetBridgeRow
canonicalNSKornLevelSetBridgeRows =
  conditionalKornLevelSetAvailableUnderHOmegaCtrlRow
  ∷ hOmegaCtrlFromNSRecordedRow
  ∷ unconditionalPromotionGatewayRecordedRow
  ∷ unconditionalPromotionRemainsFalseRow
  ∷ clayPromotionRemainsFalseRow
  ∷ []

canonicalNSKornLevelSetBridgeRowLabels :
  List String
canonicalNSKornLevelSetBridgeRowLabels =
  "conditional KornLevelSet is available under h_omega_ctrl"
  ∷ "h_omega_ctrl_from_NS is recorded"
  ∷ "unconditional promotion gateway is recorded but not opened"
  ∷ "unconditional promotion remains false"
  ∷ "Clay promotion remains false"
  ∷ []

data NSKornUnconditionalGatewayRequirement : Set where
  conditionalKornLevelSetUnderHOmegaCtrlRequirement :
    NSKornUnconditionalGatewayRequirement
  hOmegaCtrlFromNSRequirement :
    NSKornUnconditionalGatewayRequirement
  separateUnconditionalBridgeProofRequirement :
    NSKornUnconditionalGatewayRequirement

canonicalNSKornUnconditionalGatewayRequirements :
  List NSKornUnconditionalGatewayRequirement
canonicalNSKornUnconditionalGatewayRequirements =
  conditionalKornLevelSetUnderHOmegaCtrlRequirement
  ∷ hOmegaCtrlFromNSRequirement
  ∷ separateUnconditionalBridgeProofRequirement
  ∷ []

canonicalNSKornUnconditionalGatewayRequirementLabels :
  List String
canonicalNSKornUnconditionalGatewayRequirementLabels =
  "conditional KornLevelSet available under h_omega_ctrl"
  ∷ "h_omega_ctrl_from_NS recorded"
  ∷ "separate unconditional bridge proof imported"
  ∷ []

canonicalNSKornUnconditionalGatewayConditionText :
  String
canonicalNSKornUnconditionalGatewayConditionText =
  "unconditional promotion flips iff conditional KornLevelSet is available under h_omega_ctrl, h_omega_ctrl_from_NS is recorded, and a separate unconditional bridge proof is imported; this receipt records the first two requirements and keeps unconditional promotion false."

canonicalNSKornLevelSetBridgeReceiptBoundary :
  List String
canonicalNSKornLevelSetBridgeReceiptBoundary =
  "conditional KornLevelSet packet is available under h_omega_ctrl"
  ∷ "h_omega_ctrl_from_NS is recorded as the required implication"
  ∷ "unconditional promotion gateway is recorded but not opened"
  ∷ "unconditional promotion remains false"
  ∷ "Clay promotion remains false"
  ∷ []

canonicalNSKornLevelSetBridgeSummary :
  String
canonicalNSKornLevelSetBridgeSummary =
  "Fail-closed Korn bridge receipt: conditional KornLevelSet is available under h_omega_ctrl, h_omega_ctrl_from_NS is recorded, the exact unconditional-flip gateway is named, and unconditional promotion stays false."

record NSKornLevelSetUnconditionalBridgeReceipt : Setω where
  constructor mkNSKornLevelSetUnconditionalBridgeReceipt
  field
    bridgeRows :
      List NSKornLevelSetBridgeRow
    bridgeRowsAreCanonical :
      bridgeRows ≡ canonicalNSKornLevelSetBridgeRows

    bridgeRowCount :
      Nat
    bridgeRowCountIsFive :
      bridgeRowCount ≡ 5

    bridgeRowLabels :
      List String
    bridgeRowLabelsAreCanonical :
      bridgeRowLabels ≡ canonicalNSKornLevelSetBridgeRowLabels

    gatewayRequirements :
      List NSKornUnconditionalGatewayRequirement
    gatewayRequirementsAreCanonical :
      gatewayRequirements ≡ canonicalNSKornUnconditionalGatewayRequirements

    gatewayRequirementCount :
      Nat
    gatewayRequirementCountIsThree :
      gatewayRequirementCount ≡ 3

    gatewayRequirementLabels :
      List String
    gatewayRequirementLabelsAreCanonical :
      gatewayRequirementLabels ≡
      canonicalNSKornUnconditionalGatewayRequirementLabels

    gatewayConditionText :
      String
    gatewayConditionTextIsCanonical :
      gatewayConditionText ≡
      canonicalNSKornUnconditionalGatewayConditionText

    conditionalKornLevelSetAvailableUnderHOmegaCtrl :
      Bool
    conditionalKornLevelSetAvailableUnderHOmegaCtrlIsTrue :
      conditionalKornLevelSetAvailableUnderHOmegaCtrl ≡ true

    hOmegaCtrlFromNSRecorded :
      Bool
    hOmegaCtrlFromNSRecordedIsTrue :
      hOmegaCtrlFromNSRecorded ≡ true

    unconditionalPromotion :
      Bool
    unconditionalPromotionIsFalse :
      unconditionalPromotion ≡ false

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalNSKornLevelSetBridgeReceiptBoundary

    summary :
      String
    summaryIsCanonical :
      summary ≡ canonicalNSKornLevelSetBridgeSummary

open NSKornLevelSetUnconditionalBridgeReceipt public

canonicalNSKornLevelSetUnconditionalBridgeReceipt :
  NSKornLevelSetUnconditionalBridgeReceipt
canonicalNSKornLevelSetUnconditionalBridgeReceipt =
  mkNSKornLevelSetUnconditionalBridgeReceipt
    canonicalNSKornLevelSetBridgeRows
    refl
    (listLength canonicalNSKornLevelSetBridgeRows)
    refl
    canonicalNSKornLevelSetBridgeRowLabels
    refl
    canonicalNSKornUnconditionalGatewayRequirements
    refl
    (listLength canonicalNSKornUnconditionalGatewayRequirements)
    refl
    canonicalNSKornUnconditionalGatewayRequirementLabels
    refl
    canonicalNSKornUnconditionalGatewayConditionText
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    canonicalNSKornLevelSetBridgeReceiptBoundary
    refl
    canonicalNSKornLevelSetBridgeSummary
    refl

canonicalBridgeRowCountIsFive :
  bridgeRowCount canonicalNSKornLevelSetUnconditionalBridgeReceipt ≡ 5
canonicalBridgeRowCountIsFive =
  refl

canonicalGatewayRequirementCountIsThree :
  gatewayRequirementCount canonicalNSKornLevelSetUnconditionalBridgeReceipt ≡ 3
canonicalGatewayRequirementCountIsThree =
  refl

canonicalConditionalKornLevelSetAvailableUnderHOmegaCtrlIsTrue :
  conditionalKornLevelSetAvailableUnderHOmegaCtrl
    canonicalNSKornLevelSetUnconditionalBridgeReceipt
  ≡ true
canonicalConditionalKornLevelSetAvailableUnderHOmegaCtrlIsTrue =
  refl

canonicalHOmegaCtrlFromNSRecordedIsTrue :
  hOmegaCtrlFromNSRecorded canonicalNSKornLevelSetUnconditionalBridgeReceipt
  ≡ true
canonicalHOmegaCtrlFromNSRecordedIsTrue =
  refl

canonicalUnconditionalPromotionIsFalse :
  unconditionalPromotion canonicalNSKornLevelSetUnconditionalBridgeReceipt
  ≡ false
canonicalUnconditionalPromotionIsFalse =
  refl

canonicalClayPromotionIsFalse :
  clayPromotion canonicalNSKornLevelSetUnconditionalBridgeReceipt ≡ false
canonicalClayPromotionIsFalse =
  refl

canonicalGatewayConditionTextIsCanonical :
  gatewayConditionText canonicalNSKornLevelSetUnconditionalBridgeReceipt
  ≡ canonicalNSKornUnconditionalGatewayConditionText
canonicalGatewayConditionTextIsCanonical =
  refl

canonicalReceiptBoundaryIsCanonical :
  receiptBoundary canonicalNSKornLevelSetUnconditionalBridgeReceipt
  ≡ canonicalNSKornLevelSetBridgeReceiptBoundary
canonicalReceiptBoundaryIsCanonical =
  refl
