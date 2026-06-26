module DASHI.Physics.Closure.NSKornOmegaControlLayerCutoffCommutatorReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- NSKorn omega-control layer-cutoff commutator receipt.
--
-- This module is a self-contained fail-closed receipt surface for the
-- h_omega_ctrl layer cutoff commutator route.
--
-- The receipt records:
--   * localized L4 layer norms,
--   * cutoff gradient terms,
--   * the commutator route [chi, Riesz/Hessian],
--   * pressure tail separation,
--   * the absorption target into ||S||_L4(layer),
--   * the remaining smallness / constant blockers, and
--   * the explicit fail-closed status h_omega_ctrl = false and Clay = false.
--
-- No closed estimate is promoted here.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSKornOmegaControlLayerCutoffCommutatorStatus : Set where
  diagnosticOnlyLayerCutoffCommutatorRecorded :
    NSKornOmegaControlLayerCutoffCommutatorStatus

data NSKornOmegaControlLayerCutoffCommutatorStage : Set where
  localizedL4LayerNormsRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  cutoffGradientTermsRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  chiRieszCommutatorRouteRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  chiHessianCommutatorRouteRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  pressureTailSeparatedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  absorptionTargetIntoSL4LayerRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  smallnessAndConstantBlockersRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  hOmegaCtrlFalseRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage
  clayFalseRecordedStage :
    NSKornOmegaControlLayerCutoffCommutatorStage

canonicalNSKornOmegaControlLayerCutoffCommutatorStages :
  List NSKornOmegaControlLayerCutoffCommutatorStage
canonicalNSKornOmegaControlLayerCutoffCommutatorStages =
  localizedL4LayerNormsRecordedStage
  ∷ cutoffGradientTermsRecordedStage
  ∷ chiRieszCommutatorRouteRecordedStage
  ∷ chiHessianCommutatorRouteRecordedStage
  ∷ pressureTailSeparatedStage
  ∷ absorptionTargetIntoSL4LayerRecordedStage
  ∷ smallnessAndConstantBlockersRecordedStage
  ∷ hOmegaCtrlFalseRecordedStage
  ∷ clayFalseRecordedStage
  ∷ []

canonicalNSKornOmegaControlLayerCutoffCommutatorStageLabels :
  List String
canonicalNSKornOmegaControlLayerCutoffCommutatorStageLabels =
  "localized L4 layer norms are recorded"
  ∷ "cutoff gradient terms are recorded"
  ∷ "commutator route [chi, Riesz] is recorded"
  ∷ "commutator route [chi, Hessian] is recorded"
  ∷ "pressure tail separation is recorded"
  ∷ "absorption target into ||S||_L4(layer) is recorded"
  ∷ "smallness and constant blockers are recorded"
  ∷ "h_omega_ctrl is recorded false"
  ∷ "Clay is recorded false"
  ∷ []

data NSKornOmegaControlLayerCutoffCommutatorBlocker : Set where
  localizedL4LayerEstimateRemainsDiagnosticBlocker :
    NSKornOmegaControlLayerCutoffCommutatorBlocker
  cutoffGradientNotYetAbsorbedBlocker :
    NSKornOmegaControlLayerCutoffCommutatorBlocker
  chiRieszHessianCommutatorStillLocalBlocker :
    NSKornOmegaControlLayerCutoffCommutatorBlocker
  pressureTailSeparationNotYetClosedBlocker :
    NSKornOmegaControlLayerCutoffCommutatorBlocker
  smallnessConstantsStillOpenBlocker :
    NSKornOmegaControlLayerCutoffCommutatorBlocker
  hOmegaCtrlFalseBlocker :
    NSKornOmegaControlLayerCutoffCommutatorBlocker
  clayFalseBlocker :
    NSKornOmegaControlLayerCutoffCommutatorBlocker

canonicalNSKornOmegaControlLayerCutoffCommutatorBlockers :
  List NSKornOmegaControlLayerCutoffCommutatorBlocker
canonicalNSKornOmegaControlLayerCutoffCommutatorBlockers =
  localizedL4LayerEstimateRemainsDiagnosticBlocker
  ∷ cutoffGradientNotYetAbsorbedBlocker
  ∷ chiRieszHessianCommutatorStillLocalBlocker
  ∷ pressureTailSeparationNotYetClosedBlocker
  ∷ smallnessConstantsStillOpenBlocker
  ∷ hOmegaCtrlFalseBlocker
  ∷ clayFalseBlocker
  ∷ []

canonicalNSKornOmegaControlLayerCutoffCommutatorBlockerLabels :
  List String
canonicalNSKornOmegaControlLayerCutoffCommutatorBlockerLabels =
  "localized L4 layer estimate remains diagnostic"
  ∷ "cutoff gradient term is not absorbed yet"
  ∷ "commutator [chi, Riesz/Hessian] remains local"
  ∷ "pressure tail separation is not globally closed"
  ∷ "smallness constants remain open"
  ∷ "h_omega_ctrl is false"
  ∷ "Clay is false"
  ∷ []

localizedLayerL4NormText : String
localizedLayerL4NormText =
  "Localized layer norms are tracked at the L4 level as ||S||_L4(layer) and companion localized quantities."

cutoffGradientText : String
cutoffGradientText =
  "The cutoff gradient enters as a localized layer term and is kept on the same shell."

chiRieszCommutatorText : String
chiRieszCommutatorText =
  "The commutator route [chi, Riesz] is recorded as the singular-integral route for the layer cutoff estimate."

chiHessianCommutatorText : String
chiHessianCommutatorText =
  "The commutator route [chi, Hessian] is recorded as the pressure-Hessian companion of the same cutoff layer estimate."

pressureTailSeparatedText : String
pressureTailSeparatedText =
  "Pressure is split into local and tail parts; the tail stays separated and is not collapsed into a global bound here."

absorptionTargetText : String
absorptionTargetText =
  "Absorption target: the route is meant to absorb the commutator remainder into ||S||_L4(layer), but no closure is claimed."

smallnessConstantBlockerText : String
smallnessConstantBlockerText =
  "Remaining blockers are smallness and constants: the cutoff factor, the Calderon-Zygmund scale, the pressure tail weight, and the absorption slack remain open."

routeSummaryText : String
routeSummaryText =
  "NS h_omega_ctrl layer-cutoff commutator route: localized L4 layer norms, cutoff gradient terms, [chi, Riesz/Hessian] commutators, pressure tail separation, and the absorption target into ||S||_L4(layer) are all recorded, but only as a diagnostic route."

blockerSummaryText : String
blockerSummaryText =
  "The route remains fail-closed because the smallness / constant package is still open, the layer estimate is only diagnostic, and both h_omega_ctrl and Clay remain false."

receiptBoundaryText : String
receiptBoundaryText =
  "This receipt records the local commutator route only. It does not prove a closed layer absorption theorem, h_omega_ctrl promotion, or Clay promotion."

data NSKornOmegaControlLayerCutoffCommutatorPromotion : Set where

nsKornOmegaControlLayerCutoffCommutatorPromotionImpossibleHere :
  NSKornOmegaControlLayerCutoffCommutatorPromotion →
  ⊥
nsKornOmegaControlLayerCutoffCommutatorPromotionImpossibleHere ()

record NSKornOmegaControlLayerCutoffCommutatorReceipt : Setω where
  constructor mkNSKornOmegaControlLayerCutoffCommutatorReceipt
  field
    status :
      NSKornOmegaControlLayerCutoffCommutatorStatus
    statusIsCanonical :
      status ≡ diagnosticOnlyLayerCutoffCommutatorRecorded

    stageTrail :
      List NSKornOmegaControlLayerCutoffCommutatorStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSKornOmegaControlLayerCutoffCommutatorStages

    stageCount :
      Nat
    stageCountIsNine :
      stageCount ≡ 9

    stageLabels :
      List String
    stageLabelsIsCanonical :
      stageLabels ≡ canonicalNSKornOmegaControlLayerCutoffCommutatorStageLabels

    blockerTrail :
      List NSKornOmegaControlLayerCutoffCommutatorBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSKornOmegaControlLayerCutoffCommutatorBlockers

    blockerCount :
      Nat
    blockerCountIsSeven :
      blockerCount ≡ 7

    blockerLabels :
      List String
    blockerLabelsIsCanonical :
      blockerLabels ≡ canonicalNSKornOmegaControlLayerCutoffCommutatorBlockerLabels

    localizedLayerL4NormTextField :
      String
    localizedLayerL4NormTextFieldIsCanonical :
      localizedLayerL4NormTextField ≡ localizedLayerL4NormText

    cutoffGradientTextField :
      String
    cutoffGradientTextFieldIsCanonical :
      cutoffGradientTextField ≡ cutoffGradientText

    chiRieszCommutatorTextField :
      String
    chiRieszCommutatorTextFieldIsCanonical :
      chiRieszCommutatorTextField ≡ chiRieszCommutatorText

    chiHessianCommutatorTextField :
      String
    chiHessianCommutatorTextFieldIsCanonical :
      chiHessianCommutatorTextField ≡ chiHessianCommutatorText

    pressureTailSeparatedTextField :
      String
    pressureTailSeparatedTextFieldIsCanonical :
      pressureTailSeparatedTextField ≡ pressureTailSeparatedText

    absorptionTargetTextField :
      String
    absorptionTargetTextFieldIsCanonical :
      absorptionTargetTextField ≡ absorptionTargetText

    smallnessConstantBlockerTextField :
      String
    smallnessConstantBlockerTextFieldIsCanonical :
      smallnessConstantBlockerTextField ≡ smallnessConstantBlockerText

    routeSummaryTextField :
      String
    routeSummaryTextFieldIsCanonical :
      routeSummaryTextField ≡ routeSummaryText

    blockerSummaryTextField :
      String
    blockerSummaryTextFieldIsCanonical :
      blockerSummaryTextField ≡ blockerSummaryText

    receiptBoundary :
      String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

    localizedLayerL4NormRecorded :
      Bool
    localizedLayerL4NormRecordedIsTrue :
      localizedLayerL4NormRecorded ≡ true

    cutoffGradientRecorded :
      Bool
    cutoffGradientRecordedIsTrue :
      cutoffGradientRecorded ≡ true

    chiRieszCommutatorRecorded :
      Bool
    chiRieszCommutatorRecordedIsTrue :
      chiRieszCommutatorRecorded ≡ true

    chiHessianCommutatorRecorded :
      Bool
    chiHessianCommutatorRecordedIsTrue :
      chiHessianCommutatorRecorded ≡ true

    pressureTailSeparated :
      Bool
    pressureTailSeparatedIsTrue :
      pressureTailSeparated ≡ true

    absorptionTargetRecorded :
      Bool
    absorptionTargetRecordedIsTrue :
      absorptionTargetRecorded ≡ true

    smallnessConstantBlockersRemainOpen :
      Bool
    smallnessConstantBlockersRemainOpenIsTrue :
      smallnessConstantBlockersRemainOpen ≡ true

    hOmegaCtrl :
      Bool
    hOmegaCtrlIsFalse :
      hOmegaCtrl ≡ false

    clay :
      Bool
    clayIsFalse :
      clay ≡ false

open NSKornOmegaControlLayerCutoffCommutatorReceipt public

canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt :
  NSKornOmegaControlLayerCutoffCommutatorReceipt
canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt =
  mkNSKornOmegaControlLayerCutoffCommutatorReceipt
    diagnosticOnlyLayerCutoffCommutatorRecorded
    refl
    canonicalNSKornOmegaControlLayerCutoffCommutatorStages
    refl
    (listLength canonicalNSKornOmegaControlLayerCutoffCommutatorStages)
    refl
    canonicalNSKornOmegaControlLayerCutoffCommutatorStageLabels
    refl
    canonicalNSKornOmegaControlLayerCutoffCommutatorBlockers
    refl
    (listLength canonicalNSKornOmegaControlLayerCutoffCommutatorBlockers)
    refl
    canonicalNSKornOmegaControlLayerCutoffCommutatorBlockerLabels
    refl
    localizedLayerL4NormText
    refl
    cutoffGradientText
    refl
    chiRieszCommutatorText
    refl
    chiHessianCommutatorText
    refl
    pressureTailSeparatedText
    refl
    absorptionTargetText
    refl
    smallnessConstantBlockerText
    refl
    routeSummaryText
    refl
    blockerSummaryText
    refl
    receiptBoundaryText
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Projection lemmas.

canonicalStatusProjection :
  status canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt
  ≡ diagnosticOnlyLayerCutoffCommutatorRecorded
canonicalStatusProjection = refl

canonicalStageTrailProjection :
  stageTrail canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt
  ≡ canonicalNSKornOmegaControlLayerCutoffCommutatorStages
canonicalStageTrailProjection = refl

canonicalStageCountProjection :
  stageCount canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt ≡ 9
canonicalStageCountProjection = refl

canonicalBlockerTrailProjection :
  blockerTrail canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt
  ≡ canonicalNSKornOmegaControlLayerCutoffCommutatorBlockers
canonicalBlockerTrailProjection = refl

canonicalBlockerCountProjection :
  blockerCount canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt ≡ 7
canonicalBlockerCountProjection = refl

canonicalHOmegaCtrlProjection :
  hOmegaCtrl canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt ≡ false
canonicalHOmegaCtrlProjection = refl

canonicalClayProjection :
  clay canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt ≡ false
canonicalClayProjection = refl

canonicalRouteSummaryProjection :
  routeSummaryTextField canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt
  ≡ routeSummaryText
canonicalRouteSummaryProjection = refl

canonicalReceiptBoundaryProjection :
  receiptBoundary canonicalNSKornOmegaControlLayerCutoffCommutatorReceipt
  ≡ receiptBoundaryText
canonicalReceiptBoundaryProjection = refl
