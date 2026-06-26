module DASHI.Physics.Closure.NSKornConditionalLevelSetTheoremReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Explicit conditional KornLevelSet theorem receipt.
--
-- This module upgrades the earlier NSKornLevelSetHStrainDomReceipt concept
-- into a more explicit conditional theorem receipt while staying fail-closed:
-- it records the assumptions, the conditional conclusions, and the blocked
-- promotion gates, but it does not claim unconditional promotion.

data NSKornConditionalAssumption : Set where
  h_bx : NSKornConditionalAssumption
  h_gap : NSKornConditionalAssumption
  h_omega_ctrl : NSKornConditionalAssumption
  h_strain_dom : NSKornConditionalAssumption
  layerRegularity : NSKornConditionalAssumption
  biaxialBoundaryNondegeneracy : NSKornConditionalAssumption

canonicalNSKornConditionalAssumptions :
  List NSKornConditionalAssumption
canonicalNSKornConditionalAssumptions =
  h_bx
  ∷ h_gap
  ∷ h_omega_ctrl
  ∷ h_strain_dom
  ∷ layerRegularity
  ∷ biaxialBoundaryNondegeneracy
  ∷ []

canonicalNSKornConditionalAssumptionLabels :
  List String
canonicalNSKornConditionalAssumptionLabels =
  "h_bx"
  ∷ "h_gap"
  ∷ "h_omega_ctrl"
  ∷ "h_strain_dom"
  ∷ "layer regularity"
  ∷ "biaxial boundary nondegeneracy"
  ∷ []

data NSKornConditionalConclusion : Set where
  levelSetKornEstimate : NSKornConditionalConclusion
  boundaryIntegralLowerBound : NSKornConditionalConclusion

canonicalNSKornConditionalConclusions :
  List NSKornConditionalConclusion
canonicalNSKornConditionalConclusions =
  levelSetKornEstimate
  ∷ boundaryIntegralLowerBound
  ∷ []

canonicalNSKornConditionalConclusionLabels :
  List String
canonicalNSKornConditionalConclusionLabels =
  "level-set Korn estimate"
  ∷ "boundary integral lower bound"
  ∷ []

data NSKornConditionalGate : Set where
  conditionalPublishableGate : NSKornConditionalGate
  unconditionalPromotionBlockedGate : NSKornConditionalGate
  clayPromotionBlockedGate : NSKornConditionalGate
  conceptualReferenceOnlyGate : NSKornConditionalGate
  builtinOnlyGate : NSKornConditionalGate

canonicalNSKornConditionalGates :
  List NSKornConditionalGate
canonicalNSKornConditionalGates =
  conditionalPublishableGate
  ∷ unconditionalPromotionBlockedGate
  ∷ clayPromotionBlockedGate
  ∷ conceptualReferenceOnlyGate
  ∷ builtinOnlyGate
  ∷ []

canonicalNSKornConditionalGateLabels :
  List String
canonicalNSKornConditionalGateLabels =
  "conditionalPublishable=true"
  ∷ "unconditionalPromoted=false"
  ∷ "clayPromoted=false"
  ∷ "conceptual reference only"
  ∷ "self-contained builtins only"
  ∷ []

data NSKornConditionalRouteStage : Set where
  pressurePoisson : NSKornConditionalRouteStage
  calderonZygmund : NSKornConditionalRouteStage
  vorticityStrainCoupling : NSKornConditionalRouteStage

canonicalNSKornConditionalRouteStages :
  List NSKornConditionalRouteStage
canonicalNSKornConditionalRouteStages =
  pressurePoisson
  ∷ calderonZygmund
  ∷ vorticityStrainCoupling
  ∷ []

canonicalNSKornConditionalRouteStageLabels :
  List String
canonicalNSKornConditionalRouteStageLabels =
  "pressure Poisson"
  ∷ "Calderon-Zygmund"
  ∷ "vorticity-strain coupling"
  ∷ []

record NSKornConditionalLevelSetTheoremReceipt : Set where
  constructor mkNSKornConditionalLevelSetTheoremReceipt
  field
    assumptions :
      List NSKornConditionalAssumption
    assumptionsIsCanonical :
      assumptions ≡ canonicalNSKornConditionalAssumptions

    conclusions :
      List NSKornConditionalConclusion
    conclusionsIsCanonical :
      conclusions ≡ canonicalNSKornConditionalConclusions

    gates :
      List NSKornConditionalGate
    gatesIsCanonical :
      gates ≡ canonicalNSKornConditionalGates

    openRouteStages :
      List NSKornConditionalRouteStage
    openRouteStagesIsCanonical :
      openRouteStages ≡ canonicalNSKornConditionalRouteStages

    conditionalPublishableRecorded :
      Bool
    conditionalPublishableRecordedIsTrue :
      conditionalPublishableRecorded ≡ true

    unconditionalPromotedRecorded :
      Bool
    unconditionalPromotedRecordedIsFalse :
      unconditionalPromotedRecorded ≡ false

    clayPromotedRecorded :
      Bool
    clayPromotedRecordedIsFalse :
      clayPromotedRecorded ≡ false

    sourceLineageText :
      String
    sourceLineageTextIsCanonical :
      sourceLineageText ≡
      "conceptual upgrade of NSKornLevelSetHStrainDomReceipt; no import is required"

    receiptSummaryText :
      String
    receiptSummaryTextIsCanonical :
      receiptSummaryText ≡
      "conditional KornLevelSet theorem receipt with explicit h_bx, h_gap, h_omega_ctrl, h_strain_dom, layer regularity, and biaxial boundary nondegeneracy assumptions; conclusions are a level-set Korn estimate and a boundary integral lower bound; the receipt is publishable only in its conditional form and remains fail-closed for unconditional and clay promotion."

    conditionalConclusionText :
      String
    conditionalConclusionTextIsCanonical :
      conditionalConclusionText ≡
      "under the recorded assumptions, the level-set Korn estimate and the boundary integral lower bound are tracked as conditional conclusions only"

    openRouteText :
      String
    openRouteTextIsCanonical :
      openRouteText ≡
      "open route: pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling"

    gateSummaryText :
      String
    gateSummaryTextIsCanonical :
      gateSummaryText ≡
      "conditionalPublishable=true, unconditionalPromoted=false, clayPromoted=false"

    assumptionLabels :
      List String
    assumptionLabelsIsCanonical :
      assumptionLabels ≡ canonicalNSKornConditionalAssumptionLabels

    conclusionLabels :
      List String
    conclusionLabelsIsCanonical :
      conclusionLabels ≡ canonicalNSKornConditionalConclusionLabels

    gateLabels :
      List String
    gateLabelsIsCanonical :
      gateLabels ≡ canonicalNSKornConditionalGateLabels

    routeStageLabels :
      List String
    routeStageLabelsIsCanonical :
      routeStageLabels ≡ canonicalNSKornConditionalRouteStageLabels

canonicalNSKornConditionalLevelSetTheoremReceipt :
  NSKornConditionalLevelSetTheoremReceipt
canonicalNSKornConditionalLevelSetTheoremReceipt =
  mkNSKornConditionalLevelSetTheoremReceipt
    canonicalNSKornConditionalAssumptions
    refl
    canonicalNSKornConditionalConclusions
    refl
    canonicalNSKornConditionalGates
    refl
    canonicalNSKornConditionalRouteStages
    refl
    true
    refl
    false
    refl
    false
    refl
    "conceptual upgrade of NSKornLevelSetHStrainDomReceipt; no import is required"
    refl
    "conditional KornLevelSet theorem receipt with explicit h_bx, h_gap, h_omega_ctrl, h_strain_dom, layer regularity, and biaxial boundary nondegeneracy assumptions; conclusions are a level-set Korn estimate and a boundary integral lower bound; the receipt is publishable only in its conditional form and remains fail-closed for unconditional and clay promotion."
    refl
    "under the recorded assumptions, the level-set Korn estimate and the boundary integral lower bound are tracked as conditional conclusions only"
    refl
    "open route: pressure Poisson, Calderon-Zygmund, and vorticity-strain coupling"
    refl
    "conditionalPublishable=true, unconditionalPromoted=false, clayPromoted=false"
    refl
    canonicalNSKornConditionalAssumptionLabels
    refl
    canonicalNSKornConditionalConclusionLabels
    refl
    canonicalNSKornConditionalGateLabels
    refl
    canonicalNSKornConditionalRouteStageLabels
    refl

conditionalPublishableTrue :
  (receipt : NSKornConditionalLevelSetTheoremReceipt) →
  NSKornConditionalLevelSetTheoremReceipt.conditionalPublishableRecorded
    receipt
  ≡ true
conditionalPublishableTrue receipt =
  NSKornConditionalLevelSetTheoremReceipt.conditionalPublishableRecordedIsTrue
    receipt

unconditionalPromotedFalse :
  (receipt : NSKornConditionalLevelSetTheoremReceipt) →
  NSKornConditionalLevelSetTheoremReceipt.unconditionalPromotedRecorded
    receipt
  ≡ false
unconditionalPromotedFalse receipt =
  NSKornConditionalLevelSetTheoremReceipt.unconditionalPromotedRecordedIsFalse
    receipt

clayPromotedFalse :
  (receipt : NSKornConditionalLevelSetTheoremReceipt) →
  NSKornConditionalLevelSetTheoremReceipt.clayPromotedRecorded receipt
  ≡ false
clayPromotedFalse receipt =
  NSKornConditionalLevelSetTheoremReceipt.clayPromotedRecordedIsFalse
    receipt
