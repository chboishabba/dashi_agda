module DASHI.Physics.Closure.NSKornOmegaControlPressurePoissonClosureReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- NS-only h_omega_ctrl pressure/CZ route receipt.
--
-- This module is a fail-closed receipt surface for the NS-only pressure
-- Poisson / Calderon-Zygmund route.  It records the staged local route,
-- keeps the layer cutoff strictly local, and stops at the exact unclosed
-- absorption inequality
--
--   ||omega||_L4(layer) <= C ||S||_L4(layer)
--
-- without promoting any global regularity, Clay, or terminal claim.

data NSKornOmegaControlPressurePoissonStage : Set where
  pressurePoissonIdentityStage :
    NSKornOmegaControlPressurePoissonStage
  biaxialTraceIdentityStage :
    NSKornOmegaControlPressurePoissonStage
  layerCutoffLocalizationStage :
    NSKornOmegaControlPressurePoissonStage
  czHessianEstimateStage :
    NSKornOmegaControlPressurePoissonStage
  momentumEllipticCouplingStage :
    NSKornOmegaControlPressurePoissonStage
  vorticityStretchingStage :
    NSKornOmegaControlPressurePoissonStage
  exactUnclosedAbsorptionStage :
    NSKornOmegaControlPressurePoissonStage

canonicalNSKornOmegaControlPressurePoissonStageTrail :
  List NSKornOmegaControlPressurePoissonStage
canonicalNSKornOmegaControlPressurePoissonStageTrail =
  pressurePoissonIdentityStage
  ∷ biaxialTraceIdentityStage
  ∷ layerCutoffLocalizationStage
  ∷ czHessianEstimateStage
  ∷ momentumEllipticCouplingStage
  ∷ vorticityStretchingStage
  ∷ exactUnclosedAbsorptionStage
  ∷ []

data NSKornOmegaControlPressurePoissonBlocker : Set where
  pressureRouteDiagnosticOnly :
    NSKornOmegaControlPressurePoissonBlocker
  biaxialTraceRouteDiagnosticOnly :
    NSKornOmegaControlPressurePoissonBlocker
  layerCutoffRemainsLocalOnly :
    NSKornOmegaControlPressurePoissonBlocker
  czHessianEstimateRemainsLocal :
    NSKornOmegaControlPressurePoissonBlocker
  momentumCouplingStillEllipticAndOpen :
    NSKornOmegaControlPressurePoissonBlocker
  vorticityStretchingStillFeedsTheSource :
    NSKornOmegaControlPressurePoissonBlocker
  exactAbsorptionInequalityStaysUnclosed :
    NSKornOmegaControlPressurePoissonBlocker
  noGlobalRegularityInhabitant :
    NSKornOmegaControlPressurePoissonBlocker
  noClayPromotion :
    NSKornOmegaControlPressurePoissonBlocker

canonicalNSKornOmegaControlPressurePoissonBlockers :
  List NSKornOmegaControlPressurePoissonBlocker
canonicalNSKornOmegaControlPressurePoissonBlockers =
  pressureRouteDiagnosticOnly
  ∷ biaxialTraceRouteDiagnosticOnly
  ∷ layerCutoffRemainsLocalOnly
  ∷ czHessianEstimateRemainsLocal
  ∷ momentumCouplingStillEllipticAndOpen
  ∷ vorticityStretchingStillFeedsTheSource
  ∷ exactAbsorptionInequalityStaysUnclosed
  ∷ noGlobalRegularityInhabitant
  ∷ noClayPromotion
  ∷ []

data NSKornOmegaControlPressurePoissonPromotion : Set where

nsKornOmegaControlPressurePoissonPromotionImpossibleHere :
  NSKornOmegaControlPressurePoissonPromotion →
  ⊥
nsKornOmegaControlPressurePoissonPromotionImpossibleHere ()

pressurePoissonIdentityText : String
pressurePoissonIdentityText =
  "Delta p = -div div(u tensor u) on the NS-only h_omega_ctrl pressure solve."

biaxialTraceIdentityText : String
biaxialTraceIdentityText =
  "The biaxial trace identity is recorded as the pressure Hessian trace match for the local strain route."

layerCutoffLocalizationText : String
layerCutoffLocalizationText =
  "A layer cutoff localizes all norms to the active shell and does not globalize the estimate."

czHessianEstimateText : String
czHessianEstimateText =
  "The CZ Hessian estimate is used as a local singular-integral control on the pressure second derivative."

momentumEllipticCouplingText : String
momentumEllipticCouplingText =
  "The NS momentum equation is coupled through the elliptic pressure solve, not through a closed promotion step."

vorticityStretchingText : String
vorticityStretchingText =
  "Vorticity stretching is recorded as the surviving source term after the pressure and transport decomposition."

exactUnclosedAbsorptionText : String
exactUnclosedAbsorptionText =
  "||omega||_L4(layer) <= C ||S||_L4(layer) is the exact unclosed absorption inequality and remains open here."

routeSummaryText : String
routeSummaryText =
  "NS-only h_omega_ctrl pressure/CZ route: local pressure Poisson identity, local CZ Hessian estimate, elliptic coupling, and an unclosed layer absorption inequality."

blockerSummaryText : String
blockerSummaryText =
  "Blockers are explicit: the route stays diagnostic-only, the layer cutoff stays local, the CZ estimate stays local, and no global regularity or Clay promotion is inhabited."

receiptBoundaryText : String
receiptBoundaryText =
  "This receipt records the exact local route only; it does not prove a closed h_omega_ctrl absorption theorem."

record NSKornOmegaControlPressurePoissonReceipt : Setω where
  field
    stageTrail :
      List NSKornOmegaControlPressurePoissonStage

    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSKornOmegaControlPressurePoissonStageTrail

    pressurePoissonIdentityRecorded :
      Bool

    pressurePoissonIdentityRecordedIsTrue :
      pressurePoissonIdentityRecorded ≡ true

    pressurePoissonIdentity :
      String

    pressurePoissonIdentityIsCanonical :
      pressurePoissonIdentity ≡ pressurePoissonIdentityText

    biaxialTraceIdentityRecorded :
      Bool

    biaxialTraceIdentityRecordedIsTrue :
      biaxialTraceIdentityRecorded ≡ true

    biaxialTraceIdentity :
      String

    biaxialTraceIdentityIsCanonical :
      biaxialTraceIdentity ≡ biaxialTraceIdentityText

    layerCutoffLocalizationRecorded :
      Bool

    layerCutoffLocalizationRecordedIsTrue :
      layerCutoffLocalizationRecorded ≡ true

    layerCutoffLocalization :
      String

    layerCutoffLocalizationIsCanonical :
      layerCutoffLocalization ≡ layerCutoffLocalizationText

    czHessianEstimateRecorded :
      Bool

    czHessianEstimateRecordedIsTrue :
      czHessianEstimateRecorded ≡ true

    czHessianEstimate :
      String

    czHessianEstimateIsCanonical :
      czHessianEstimate ≡ czHessianEstimateText

    momentumEllipticCouplingRecorded :
      Bool

    momentumEllipticCouplingRecordedIsTrue :
      momentumEllipticCouplingRecorded ≡ true

    momentumEllipticCoupling :
      String

    momentumEllipticCouplingIsCanonical :
      momentumEllipticCoupling ≡ momentumEllipticCouplingText

    vorticityStretchingRecorded :
      Bool

    vorticityStretchingRecordedIsTrue :
      vorticityStretchingRecorded ≡ true

    vorticityStretching :
      String

    vorticityStretchingIsCanonical :
      vorticityStretching ≡ vorticityStretchingText

    exactUnclosedAbsorptionRecorded :
      Bool

    exactUnclosedAbsorptionRecordedIsTrue :
      exactUnclosedAbsorptionRecorded ≡ true

    exactUnclosedAbsorptionInequality :
      String

    exactUnclosedAbsorptionInequalityIsCanonical :
      exactUnclosedAbsorptionInequality ≡ exactUnclosedAbsorptionText

    routeSummary :
      String

    routeSummaryIsCanonical :
      routeSummary ≡ routeSummaryText

    blockerSummary :
      String

    blockerSummaryIsCanonical :
      blockerSummary ≡ blockerSummaryText

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

    blockerTrail :
      List NSKornOmegaControlPressurePoissonBlocker

    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSKornOmegaControlPressurePoissonBlockers

    pressurePoissonRouteStillLocal :
      Bool

    pressurePoissonRouteStillLocalIsTrue :
      pressurePoissonRouteStillLocal ≡ true

    czRouteStillLocal :
      Bool

    czRouteStillLocalIsTrue :
      czRouteStillLocal ≡ true

    layerCutoffRemainsLocal :
      Bool

    layerCutoffRemainsLocalIsTrue :
      layerCutoffRemainsLocal ≡ true

    exactAbsorptionStillUnclosed :
      Bool

    exactAbsorptionStillUnclosedIsTrue :
      exactAbsorptionStillUnclosed ≡ true

    pressurePoissonPromotionRequested :
      Bool

    pressurePoissonPromotionRequestedIsFalse :
      pressurePoissonPromotionRequested ≡ false

    czPromotionRequested :
      Bool

    czPromotionRequestedIsFalse :
      czPromotionRequested ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    promotionClaims :
      List NSKornOmegaControlPressurePoissonPromotion

    promotionClaimsAreEmpty :
      promotionClaims ≡ []

    noPromotionPossibleHere :
      NSKornOmegaControlPressurePoissonPromotion →
      ⊥

open NSKornOmegaControlPressurePoissonReceipt public

canonicalNSKornOmegaControlPressurePoissonReceipt :
  NSKornOmegaControlPressurePoissonReceipt
canonicalNSKornOmegaControlPressurePoissonReceipt =
  record
    { stageTrail =
        canonicalNSKornOmegaControlPressurePoissonStageTrail
    ; stageTrailIsCanonical =
        refl
    ; pressurePoissonIdentityRecorded =
        true
    ; pressurePoissonIdentityRecordedIsTrue =
        refl
    ; pressurePoissonIdentity =
        pressurePoissonIdentityText
    ; pressurePoissonIdentityIsCanonical =
        refl
    ; biaxialTraceIdentityRecorded =
        true
    ; biaxialTraceIdentityRecordedIsTrue =
        refl
    ; biaxialTraceIdentity =
        biaxialTraceIdentityText
    ; biaxialTraceIdentityIsCanonical =
        refl
    ; layerCutoffLocalizationRecorded =
        true
    ; layerCutoffLocalizationRecordedIsTrue =
        refl
    ; layerCutoffLocalization =
        layerCutoffLocalizationText
    ; layerCutoffLocalizationIsCanonical =
        refl
    ; czHessianEstimateRecorded =
        true
    ; czHessianEstimateRecordedIsTrue =
        refl
    ; czHessianEstimate =
        czHessianEstimateText
    ; czHessianEstimateIsCanonical =
        refl
    ; momentumEllipticCouplingRecorded =
        true
    ; momentumEllipticCouplingRecordedIsTrue =
        refl
    ; momentumEllipticCoupling =
        momentumEllipticCouplingText
    ; momentumEllipticCouplingIsCanonical =
        refl
    ; vorticityStretchingRecorded =
        true
    ; vorticityStretchingRecordedIsTrue =
        refl
    ; vorticityStretching =
        vorticityStretchingText
    ; vorticityStretchingIsCanonical =
        refl
    ; exactUnclosedAbsorptionRecorded =
        true
    ; exactUnclosedAbsorptionRecordedIsTrue =
        refl
    ; exactUnclosedAbsorptionInequality =
        exactUnclosedAbsorptionText
    ; exactUnclosedAbsorptionInequalityIsCanonical =
        refl
    ; routeSummary =
        routeSummaryText
    ; routeSummaryIsCanonical =
        refl
    ; blockerSummary =
        blockerSummaryText
    ; blockerSummaryIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSKornOmegaControlPressurePoissonBlockers
    ; blockerTrailIsCanonical =
        refl
    ; pressurePoissonRouteStillLocal =
        true
    ; pressurePoissonRouteStillLocalIsTrue =
        refl
    ; czRouteStillLocal =
        true
    ; czRouteStillLocalIsTrue =
        refl
    ; layerCutoffRemainsLocal =
        true
    ; layerCutoffRemainsLocalIsTrue =
        refl
    ; exactAbsorptionStillUnclosed =
        true
    ; exactAbsorptionStillUnclosedIsTrue =
        refl
    ; pressurePoissonPromotionRequested =
        false
    ; pressurePoissonPromotionRequestedIsFalse =
        refl
    ; czPromotionRequested =
        false
    ; czPromotionRequestedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; promotionClaims =
        []
    ; promotionClaimsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsKornOmegaControlPressurePoissonPromotionImpossibleHere
    }
