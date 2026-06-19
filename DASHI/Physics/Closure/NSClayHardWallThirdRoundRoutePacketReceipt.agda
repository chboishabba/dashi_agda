module DASHI.Physics.Closure.NSClayHardWallThirdRoundRoutePacketReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Third-round route packet receipt for the NS Clay hard-wall route.
--
-- This file is self-contained and label-only.  It aggregates the second-
-- round route packet together with five new expected surfaces from this
-- round, records the dependency edges between them, and keeps the four
-- analytic promotion flags that matter here fail-closed:
-- h_omega_ctrl, QGronwall, collapseImpossible, and Clay all remain false.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Canonical stages.

data NSClayHardWallThirdRoundStage : Set where
  secondRoundRoutePacket :
    NSClayHardWallThirdRoundStage
  hOmegaCtrlExpectedSurface :
    NSClayHardWallThirdRoundStage
  qGronwallExpectedSurface :
    NSClayHardWallThirdRoundStage
  collapseImpossibleExpectedSurface :
    NSClayHardWallThirdRoundStage
  clayExpectedSurface :
    NSClayHardWallThirdRoundStage
  dependencyProjectionExpectedSurface :
    NSClayHardWallThirdRoundStage

canonicalNSClayHardWallThirdRoundStages :
  List NSClayHardWallThirdRoundStage
canonicalNSClayHardWallThirdRoundStages =
  secondRoundRoutePacket
  ∷ hOmegaCtrlExpectedSurface
  ∷ qGronwallExpectedSurface
  ∷ collapseImpossibleExpectedSurface
  ∷ clayExpectedSurface
  ∷ dependencyProjectionExpectedSurface
  ∷ []

stageLabel : NSClayHardWallThirdRoundStage → String
stageLabel secondRoundRoutePacket =
  "NSClayHardWallSecondRoundRoutePacketReceipt"
stageLabel hOmegaCtrlExpectedSurface =
  "h_omega_ctrl expected surface"
stageLabel qGronwallExpectedSurface =
  "QGronwall expected surface"
stageLabel collapseImpossibleExpectedSurface =
  "collapseImpossible expected surface"
stageLabel clayExpectedSurface =
  "Clay expected surface"
stageLabel dependencyProjectionExpectedSurface =
  "dependency-projection expected surface"

canonicalNSClayHardWallThirdRoundStageLabels : List String
canonicalNSClayHardWallThirdRoundStageLabels =
  "NSClayHardWallSecondRoundRoutePacketReceipt"
  ∷ "h_omega_ctrl expected surface"
  ∷ "QGronwall expected surface"
  ∷ "collapseImpossible expected surface"
  ∷ "Clay expected surface"
  ∷ "dependency-projection expected surface"
  ∷ []

------------------------------------------------------------------------
-- Canonical gates.

data NSClayHardWallThirdRoundGate : Set where
  hOmegaCtrlStillFalse :
    NSClayHardWallThirdRoundGate
  qGronwallStillFalse :
    NSClayHardWallThirdRoundGate
  collapseImpossibleStillFalse :
    NSClayHardWallThirdRoundGate
  clayStillFalse :
    NSClayHardWallThirdRoundGate
  dependencyProjectionStillFalse :
    NSClayHardWallThirdRoundGate

canonicalNSClayHardWallThirdRoundGates :
  List NSClayHardWallThirdRoundGate
canonicalNSClayHardWallThirdRoundGates =
  hOmegaCtrlStillFalse
  ∷ qGronwallStillFalse
  ∷ collapseImpossibleStillFalse
  ∷ clayStillFalse
  ∷ dependencyProjectionStillFalse
  ∷ []

gateLabel : NSClayHardWallThirdRoundGate → String
gateLabel hOmegaCtrlStillFalse =
  "h_omega_ctrl remains false"
gateLabel qGronwallStillFalse =
  "QGronwall remains false"
gateLabel collapseImpossibleStillFalse =
  "collapseImpossible remains false"
gateLabel clayStillFalse =
  "Clay remains false"
gateLabel dependencyProjectionStillFalse =
  "dependency projection remains false"

canonicalNSClayHardWallThirdRoundGateLabels : List String
canonicalNSClayHardWallThirdRoundGateLabels =
  "h_omega_ctrl remains false"
  ∷ "QGronwall remains false"
  ∷ "collapseImpossible remains false"
  ∷ "Clay remains false"
  ∷ "dependency projection remains false"
  ∷ []

------------------------------------------------------------------------
-- Canonical projections.

data NSClayHardWallThirdRoundProjection : Set where
  secondRoundRoutePacketProjection :
    NSClayHardWallThirdRoundProjection
  hOmegaCtrlProjection :
    NSClayHardWallThirdRoundProjection
  qGronwallProjection :
    NSClayHardWallThirdRoundProjection
  collapseImpossibleProjection :
    NSClayHardWallThirdRoundProjection
  clayProjection :
    NSClayHardWallThirdRoundProjection
  dependencyEdgeProjection :
    NSClayHardWallThirdRoundProjection

canonicalNSClayHardWallThirdRoundProjections :
  List NSClayHardWallThirdRoundProjection
canonicalNSClayHardWallThirdRoundProjections =
  secondRoundRoutePacketProjection
  ∷ hOmegaCtrlProjection
  ∷ qGronwallProjection
  ∷ collapseImpossibleProjection
  ∷ clayProjection
  ∷ dependencyEdgeProjection
  ∷ []

projectionLabel : NSClayHardWallThirdRoundProjection → String
projectionLabel secondRoundRoutePacketProjection =
  "route packet projection"
projectionLabel hOmegaCtrlProjection =
  "h_omega_ctrl projection"
projectionLabel qGronwallProjection =
  "QGronwall projection"
projectionLabel collapseImpossibleProjection =
  "collapseImpossible projection"
projectionLabel clayProjection =
  "Clay projection"
projectionLabel dependencyEdgeProjection =
  "dependency-edge projection"

canonicalNSClayHardWallThirdRoundProjectionLabels : List String
canonicalNSClayHardWallThirdRoundProjectionLabels =
  "route packet projection"
  ∷ "h_omega_ctrl projection"
  ∷ "QGronwall projection"
  ∷ "collapseImpossible projection"
  ∷ "Clay projection"
  ∷ "dependency-edge projection"
  ∷ []

------------------------------------------------------------------------
-- Dependency edges.

data NSClayHardWallThirdRoundDependencyEdge : Set where
  secondRoundToHOmegaCtrl :
    NSClayHardWallThirdRoundDependencyEdge
  secondRoundToQGronwall :
    NSClayHardWallThirdRoundDependencyEdge
  secondRoundToCollapseImpossible :
    NSClayHardWallThirdRoundDependencyEdge
  secondRoundToClay :
    NSClayHardWallThirdRoundDependencyEdge
  secondRoundToDependencyProjection :
    NSClayHardWallThirdRoundDependencyEdge

canonicalNSClayHardWallThirdRoundDependencyEdges :
  List NSClayHardWallThirdRoundDependencyEdge
canonicalNSClayHardWallThirdRoundDependencyEdges =
  secondRoundToHOmegaCtrl
  ∷ secondRoundToQGronwall
  ∷ secondRoundToCollapseImpossible
  ∷ secondRoundToClay
  ∷ secondRoundToDependencyProjection
  ∷ []

dependencyEdgeLabel :
  NSClayHardWallThirdRoundDependencyEdge → String
dependencyEdgeLabel secondRoundToHOmegaCtrl =
  "NSClayHardWallSecondRoundRoutePacketReceipt -> h_omega_ctrl expected surface"
dependencyEdgeLabel secondRoundToQGronwall =
  "NSClayHardWallSecondRoundRoutePacketReceipt -> QGronwall expected surface"
dependencyEdgeLabel secondRoundToCollapseImpossible =
  "NSClayHardWallSecondRoundRoutePacketReceipt -> collapseImpossible expected surface"
dependencyEdgeLabel secondRoundToClay =
  "NSClayHardWallSecondRoundRoutePacketReceipt -> Clay expected surface"
dependencyEdgeLabel secondRoundToDependencyProjection =
  "NSClayHardWallSecondRoundRoutePacketReceipt -> dependency-projection expected surface"

canonicalNSClayHardWallThirdRoundDependencyEdgeLabels :
  List String
canonicalNSClayHardWallThirdRoundDependencyEdgeLabels =
  "NSClayHardWallSecondRoundRoutePacketReceipt -> h_omega_ctrl expected surface"
  ∷ "NSClayHardWallSecondRoundRoutePacketReceipt -> QGronwall expected surface"
  ∷ "NSClayHardWallSecondRoundRoutePacketReceipt -> collapseImpossible expected surface"
  ∷ "NSClayHardWallSecondRoundRoutePacketReceipt -> Clay expected surface"
  ∷ "NSClayHardWallSecondRoundRoutePacketReceipt -> dependency-projection expected surface"
  ∷ []

------------------------------------------------------------------------
-- Boundary statement.

thirdRoundRoutePacketStatement : String
thirdRoundRoutePacketStatement =
  "Third-round hard-wall receipt: the second-round route packet remains the dependency root, five new expected surfaces are named as label-only projections, the dependency edges are recorded explicitly, and h_omega_ctrl, QGronwall, collapseImpossible, and Clay remain false."

thirdRoundRoutePacketBoundary : List String
thirdRoundRoutePacketBoundary =
  "second-round route packet stays as the root receipt"
  ∷ "five new expected surfaces are named without importing worker modules"
  ∷ "dependency edges are recorded as label strings only"
  ∷ "h_omega_ctrl remains false"
  ∷ "QGronwall remains false"
  ∷ "collapseImpossible remains false"
  ∷ "Clay remains false"
  ∷ "projection labels stay canonical and self-contained"
  ∷ []

------------------------------------------------------------------------
-- Receipt record.

record NSClayHardWallThirdRoundRoutePacketReceipt : Setω where
  field
    referenceRoutePacket :
      String
    referenceRoutePacketIsCanonical :
      referenceRoutePacket ≡ "NSClayHardWallSecondRoundRoutePacketReceipt"

    routeStages :
      List NSClayHardWallThirdRoundStage
    routeStagesAreCanonical :
      routeStages ≡ canonicalNSClayHardWallThirdRoundStages

    routeStageLabels :
      List String
    routeStageLabelsAreCanonical :
      routeStageLabels ≡ canonicalNSClayHardWallThirdRoundStageLabels

    routeStageCount :
      Nat
    routeStageCountIsSix :
      routeStageCount ≡ 6

    routeGates :
      List NSClayHardWallThirdRoundGate
    routeGatesAreCanonical :
      routeGates ≡ canonicalNSClayHardWallThirdRoundGates

    routeGateLabels :
      List String
    routeGateLabelsAreCanonical :
      routeGateLabels ≡ canonicalNSClayHardWallThirdRoundGateLabels

    routeGateCount :
      Nat
    routeGateCountIsFive :
      routeGateCount ≡ 5

    routeProjections :
      List NSClayHardWallThirdRoundProjection
    routeProjectionsAreCanonical :
      routeProjections ≡ canonicalNSClayHardWallThirdRoundProjections

    routeProjectionLabels :
      List String
    routeProjectionLabelsAreCanonical :
      routeProjectionLabels ≡ canonicalNSClayHardWallThirdRoundProjectionLabels

    routeProjectionCount :
      Nat
    routeProjectionCountIsSix :
      routeProjectionCount ≡ 6

    dependencyEdges :
      List NSClayHardWallThirdRoundDependencyEdge
    dependencyEdgesAreCanonical :
      dependencyEdges ≡ canonicalNSClayHardWallThirdRoundDependencyEdges

    dependencyEdgeLabels :
      List String
    dependencyEdgeLabelsAreCanonical :
      dependencyEdgeLabels ≡ canonicalNSClayHardWallThirdRoundDependencyEdgeLabels

    dependencyEdgeCount :
      Nat
    dependencyEdgeCountIsFive :
      dependencyEdgeCount ≡ 5

    statement :
      String
    statementIsCanonical :
      statement ≡ thirdRoundRoutePacketStatement

    hOmegaCtrlPromoted :
      Bool
    hOmegaCtrlPromotedIsFalse :
      hOmegaCtrlPromoted ≡ false

    qGronwallPromoted :
      Bool
    qGronwallPromotedIsFalse :
      qGronwallPromoted ≡ false

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
      receiptBoundary ≡ thirdRoundRoutePacketBoundary

open NSClayHardWallThirdRoundRoutePacketReceipt public

canonicalNSClayHardWallThirdRoundRoutePacketReceipt :
  NSClayHardWallThirdRoundRoutePacketReceipt
canonicalNSClayHardWallThirdRoundRoutePacketReceipt =
  record
    { referenceRoutePacket =
        "NSClayHardWallSecondRoundRoutePacketReceipt"
    ; referenceRoutePacketIsCanonical =
        refl
    ; routeStages =
        canonicalNSClayHardWallThirdRoundStages
    ; routeStagesAreCanonical =
        refl
    ; routeStageLabels =
        canonicalNSClayHardWallThirdRoundStageLabels
    ; routeStageLabelsAreCanonical =
        refl
    ; routeStageCount =
        listLength canonicalNSClayHardWallThirdRoundStages
    ; routeStageCountIsSix =
        refl
    ; routeGates =
        canonicalNSClayHardWallThirdRoundGates
    ; routeGatesAreCanonical =
        refl
    ; routeGateLabels =
        canonicalNSClayHardWallThirdRoundGateLabels
    ; routeGateLabelsAreCanonical =
        refl
    ; routeGateCount =
        listLength canonicalNSClayHardWallThirdRoundGates
    ; routeGateCountIsFive =
        refl
    ; routeProjections =
        canonicalNSClayHardWallThirdRoundProjections
    ; routeProjectionsAreCanonical =
        refl
    ; routeProjectionLabels =
        canonicalNSClayHardWallThirdRoundProjectionLabels
    ; routeProjectionLabelsAreCanonical =
        refl
    ; routeProjectionCount =
        listLength canonicalNSClayHardWallThirdRoundProjections
    ; routeProjectionCountIsSix =
        refl
    ; dependencyEdges =
        canonicalNSClayHardWallThirdRoundDependencyEdges
    ; dependencyEdgesAreCanonical =
        refl
    ; dependencyEdgeLabels =
        canonicalNSClayHardWallThirdRoundDependencyEdgeLabels
    ; dependencyEdgeLabelsAreCanonical =
        refl
    ; dependencyEdgeCount =
        listLength canonicalNSClayHardWallThirdRoundDependencyEdges
    ; dependencyEdgeCountIsFive =
        refl
    ; statement =
        thirdRoundRoutePacketStatement
    ; statementIsCanonical =
        refl
    ; hOmegaCtrlPromoted =
        false
    ; hOmegaCtrlPromotedIsFalse =
        refl
    ; qGronwallPromoted =
        false
    ; qGronwallPromotedIsFalse =
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
        thirdRoundRoutePacketBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

------------------------------------------------------------------------
-- Record projections.

thirdRoundRouteStageCountIsSix :
  routeStageCount canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ 6
thirdRoundRouteStageCountIsSix =
  refl

thirdRoundRouteGateCountIsFive :
  routeGateCount canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ 5
thirdRoundRouteGateCountIsFive =
  refl

thirdRoundRouteProjectionCountIsSix :
  routeProjectionCount
    canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ 6
thirdRoundRouteProjectionCountIsSix =
  refl

thirdRoundDependencyEdgeCountIsFive :
  dependencyEdgeCount
    canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ 5
thirdRoundDependencyEdgeCountIsFive =
  refl

thirdRoundHOmegaCtrlPromotedIsFalse :
  hOmegaCtrlPromoted canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ false
thirdRoundHOmegaCtrlPromotedIsFalse =
  refl

thirdRoundQGronwallPromotedIsFalse :
  qGronwallPromoted canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ false
thirdRoundQGronwallPromotedIsFalse =
  refl

thirdRoundCollapseImpossiblePromotedIsFalse :
  collapseImpossiblePromoted
    canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ false
thirdRoundCollapseImpossiblePromotedIsFalse =
  refl

thirdRoundClayPromotedIsFalse :
  clayPromoted canonicalNSClayHardWallThirdRoundRoutePacketReceipt
  ≡ false
thirdRoundClayPromotedIsFalse =
  refl
