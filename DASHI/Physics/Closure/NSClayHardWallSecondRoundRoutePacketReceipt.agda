module DASHI.Physics.Closure.NSClayHardWallSecondRoundRoutePacketReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Second-round route packet for the two remaining NS Clay hard walls.
--
-- This packet normalizes the surfaces added after the first hard-wall
-- packet at 38f800d7.  It remains fail-closed: the new modules sharpen
-- the pressure/CZ h_omega_ctrl route and the collapse Q(t)/absorption
-- route, but they do not inhabit KornLevelSet, collapseImpossible, or
-- Clay promotion.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSClayHardWallSecondRoundSurface : Set where
  firstRoundRoutePacket :
    NSClayHardWallSecondRoundSurface
  kornPressurePoissonClosure :
    NSClayHardWallSecondRoundSurface
  kornUnconditionalBridge :
    NSClayHardWallSecondRoundSurface
  collapseQCommutatorEstimate :
    NSClayHardWallSecondRoundSurface
  collapseRatioAbsorptionCriterion :
    NSClayHardWallSecondRoundSurface
  postCalc11HardWallStateAggregation :
    NSClayHardWallSecondRoundSurface
  standardProofObligations :
    NSClayHardWallSecondRoundSurface

canonicalNSClayHardWallSecondRoundSurfaces :
  List NSClayHardWallSecondRoundSurface
canonicalNSClayHardWallSecondRoundSurfaces =
  firstRoundRoutePacket
  ∷ kornPressurePoissonClosure
  ∷ kornUnconditionalBridge
  ∷ collapseQCommutatorEstimate
  ∷ collapseRatioAbsorptionCriterion
  ∷ postCalc11HardWallStateAggregation
  ∷ standardProofObligations
  ∷ []

surfaceLabel : NSClayHardWallSecondRoundSurface → String
surfaceLabel firstRoundRoutePacket =
  "NSClayHardWallRoutePacketReceipt"
surfaceLabel kornPressurePoissonClosure =
  "NSKornOmegaControlPressurePoissonClosureReceipt"
surfaceLabel kornUnconditionalBridge =
  "NSKornLevelSetUnconditionalBridgeReceipt"
surfaceLabel collapseQCommutatorEstimate =
  "NSCollapseBoundaryQCommutatorEstimateReceipt"
surfaceLabel collapseRatioAbsorptionCriterion =
  "NSCollapseRatioAbsorptionCriterionReceipt"
surfaceLabel postCalc11HardWallStateAggregation =
  "NSClayPostCalc11HardWallStateAggregationReceipt"
surfaceLabel standardProofObligations =
  "NSClayHardWallStandardProofObligationsReceipt"

canonicalNSClayHardWallSecondRoundSurfaceLabels : List String
canonicalNSClayHardWallSecondRoundSurfaceLabels =
  "NSClayHardWallRoutePacketReceipt"
  ∷ "NSKornOmegaControlPressurePoissonClosureReceipt"
  ∷ "NSKornLevelSetUnconditionalBridgeReceipt"
  ∷ "NSCollapseBoundaryQCommutatorEstimateReceipt"
  ∷ "NSCollapseRatioAbsorptionCriterionReceipt"
  ∷ "NSClayPostCalc11HardWallStateAggregationReceipt"
  ∷ "NSClayHardWallStandardProofObligationsReceipt"
  ∷ []

data NSClayHardWallSecondRoundGate : Set where
  hOmegaCtrlPressureCZRouteSharpened :
    NSClayHardWallSecondRoundGate
  hOmegaCtrlAbsorptionStillOpen :
    NSClayHardWallSecondRoundGate
  unconditionalKornBridgeStillClosed :
    NSClayHardWallSecondRoundGate
  qCommutatorDerivativeBookkeepingSharpened :
    NSClayHardWallSecondRoundGate
  qCommutatorEstimateStillOpen :
    NSClayHardWallSecondRoundGate
  ratioAbsorptionCriterionRecorded :
    NSClayHardWallSecondRoundGate
  collapseImpossibleStillOpen :
    NSClayHardWallSecondRoundGate
  clayPromotionStillFalse :
    NSClayHardWallSecondRoundGate

canonicalNSClayHardWallSecondRoundGates :
  List NSClayHardWallSecondRoundGate
canonicalNSClayHardWallSecondRoundGates =
  hOmegaCtrlPressureCZRouteSharpened
  ∷ hOmegaCtrlAbsorptionStillOpen
  ∷ unconditionalKornBridgeStillClosed
  ∷ qCommutatorDerivativeBookkeepingSharpened
  ∷ qCommutatorEstimateStillOpen
  ∷ ratioAbsorptionCriterionRecorded
  ∷ collapseImpossibleStillOpen
  ∷ clayPromotionStillFalse
  ∷ []

gateLabel : NSClayHardWallSecondRoundGate → String
gateLabel hOmegaCtrlPressureCZRouteSharpened =
  "h_omega_ctrl pressure/CZ route sharpened"
gateLabel hOmegaCtrlAbsorptionStillOpen =
  "h_omega_ctrl absorption still open"
gateLabel unconditionalKornBridgeStillClosed =
  "unconditional Korn bridge still closed"
gateLabel qCommutatorDerivativeBookkeepingSharpened =
  "Q commutator derivative bookkeeping sharpened"
gateLabel qCommutatorEstimateStillOpen =
  "Q commutator estimate still open"
gateLabel ratioAbsorptionCriterionRecorded =
  "ratio absorption criterion recorded"
gateLabel collapseImpossibleStillOpen =
  "collapseImpossible still open"
gateLabel clayPromotionStillFalse =
  "Clay promotion still false"

canonicalNSClayHardWallSecondRoundGateLabels : List String
canonicalNSClayHardWallSecondRoundGateLabels =
  "h_omega_ctrl pressure/CZ route sharpened"
  ∷ "h_omega_ctrl absorption still open"
  ∷ "unconditional Korn bridge still closed"
  ∷ "Q commutator derivative bookkeeping sharpened"
  ∷ "Q commutator estimate still open"
  ∷ "ratio absorption criterion recorded"
  ∷ "collapseImpossible still open"
  ∷ "Clay promotion still false"
  ∷ []

secondRoundRoutePacketStatement : String
secondRoundRoutePacketStatement =
  "Second-round hard-wall packet: the h_omega_ctrl route now records pressure/CZ localization and the exact unclosed absorption inequality, while the collapse route now records the Q commutator derivative terms and ratio absorption criterion; all hard analytic gates remain fail-closed."

secondRoundRoutePacketBoundary : List String
secondRoundRoutePacketBoundary =
  "first hard-wall packet at 38f800d7 remains the base route packet"
  ∷ "pressure/CZ h_omega_ctrl absorption inequality remains open"
  ∷ "unconditional KornLevelSet bridge remains false"
  ∷ "Q(t) commutator estimate remains open"
  ∷ "ratio absorption criterion is recorded but depends on Q/Sobolev closure"
  ∷ "collapseImpossible remains false"
  ∷ "Clay promotion remains false"
  ∷ []

record NSClayHardWallSecondRoundRoutePacketReceipt : Setω where
  field
    referenceCommit :
      String
    referenceCommitIsCanonical :
      referenceCommit ≡ "38f800d7"

    routeSurfaces :
      List NSClayHardWallSecondRoundSurface
    routeSurfacesAreCanonical :
      routeSurfaces ≡ canonicalNSClayHardWallSecondRoundSurfaces

    routeSurfaceLabels :
      List String
    routeSurfaceLabelsAreCanonical :
      routeSurfaceLabels ≡ canonicalNSClayHardWallSecondRoundSurfaceLabels

    routeSurfaceCount :
      Nat
    routeSurfaceCountIsSeven :
      routeSurfaceCount ≡ 7

    routeGates :
      List NSClayHardWallSecondRoundGate
    routeGatesAreCanonical :
      routeGates ≡ canonicalNSClayHardWallSecondRoundGates

    routeGateLabels :
      List String
    routeGateLabelsAreCanonical :
      routeGateLabels ≡ canonicalNSClayHardWallSecondRoundGateLabels

    routeGateCount :
      Nat
    routeGateCountIsEight :
      routeGateCount ≡ 8

    statement :
      String
    statementIsCanonical :
      statement ≡ secondRoundRoutePacketStatement

    hOmegaCtrlPromoted :
      Bool
    hOmegaCtrlPromotedIsFalse :
      hOmegaCtrlPromoted ≡ false

    kornLevelSetUnconditionalPromoted :
      Bool
    kornLevelSetUnconditionalPromotedIsFalse :
      kornLevelSetUnconditionalPromoted ≡ false

    qCommutatorEstimatePromoted :
      Bool
    qCommutatorEstimatePromotedIsFalse :
      qCommutatorEstimatePromoted ≡ false

    collapseImpossiblePromoted :
      Bool
    collapseImpossiblePromotedIsFalse :
      collapseImpossiblePromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ secondRoundRoutePacketBoundary

open NSClayHardWallSecondRoundRoutePacketReceipt public

canonicalNSClayHardWallSecondRoundRoutePacketReceipt :
  NSClayHardWallSecondRoundRoutePacketReceipt
canonicalNSClayHardWallSecondRoundRoutePacketReceipt =
  record
    { referenceCommit =
        "38f800d7"
    ; referenceCommitIsCanonical =
        refl
    ; routeSurfaces =
        canonicalNSClayHardWallSecondRoundSurfaces
    ; routeSurfacesAreCanonical =
        refl
    ; routeSurfaceLabels =
        canonicalNSClayHardWallSecondRoundSurfaceLabels
    ; routeSurfaceLabelsAreCanonical =
        refl
    ; routeSurfaceCount =
        listLength canonicalNSClayHardWallSecondRoundSurfaces
    ; routeSurfaceCountIsSeven =
        refl
    ; routeGates =
        canonicalNSClayHardWallSecondRoundGates
    ; routeGatesAreCanonical =
        refl
    ; routeGateLabels =
        canonicalNSClayHardWallSecondRoundGateLabels
    ; routeGateLabelsAreCanonical =
        refl
    ; routeGateCount =
        listLength canonicalNSClayHardWallSecondRoundGates
    ; routeGateCountIsEight =
        refl
    ; statement =
        secondRoundRoutePacketStatement
    ; statementIsCanonical =
        refl
    ; hOmegaCtrlPromoted =
        false
    ; hOmegaCtrlPromotedIsFalse =
        refl
    ; kornLevelSetUnconditionalPromoted =
        false
    ; kornLevelSetUnconditionalPromotedIsFalse =
        refl
    ; qCommutatorEstimatePromoted =
        false
    ; qCommutatorEstimatePromotedIsFalse =
        refl
    ; collapseImpossiblePromoted =
        false
    ; collapseImpossiblePromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; receiptBoundary =
        secondRoundRoutePacketBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

secondRoundRouteSurfaceCountIsSeven :
  routeSurfaceCount canonicalNSClayHardWallSecondRoundRoutePacketReceipt
  ≡ 7
secondRoundRouteSurfaceCountIsSeven =
  refl

secondRoundRouteGateCountIsEight :
  routeGateCount canonicalNSClayHardWallSecondRoundRoutePacketReceipt
  ≡ 8
secondRoundRouteGateCountIsEight =
  refl

secondRoundHOmegaCtrlPromotedIsFalse :
  hOmegaCtrlPromoted canonicalNSClayHardWallSecondRoundRoutePacketReceipt
  ≡ false
secondRoundHOmegaCtrlPromotedIsFalse =
  refl

secondRoundKornLevelSetUnconditionalPromotedIsFalse :
  kornLevelSetUnconditionalPromoted
    canonicalNSClayHardWallSecondRoundRoutePacketReceipt
  ≡ false
secondRoundKornLevelSetUnconditionalPromotedIsFalse =
  refl

secondRoundQCommutatorEstimatePromotedIsFalse :
  qCommutatorEstimatePromoted
    canonicalNSClayHardWallSecondRoundRoutePacketReceipt
  ≡ false
secondRoundQCommutatorEstimatePromotedIsFalse =
  refl

secondRoundCollapseImpossiblePromotedIsFalse :
  collapseImpossiblePromoted
    canonicalNSClayHardWallSecondRoundRoutePacketReceipt
  ≡ false
secondRoundCollapseImpossiblePromotedIsFalse =
  refl

secondRoundClayPromotedIsFalse :
  clayPromoted canonicalNSClayHardWallSecondRoundRoutePacketReceipt
  ≡ false
secondRoundClayPromotedIsFalse =
  refl
