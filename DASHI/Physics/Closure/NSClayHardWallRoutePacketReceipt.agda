module DASHI.Physics.Closure.NSClayHardWallRoutePacketReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only route packet for the two remaining NS Clay hard walls.
--
-- This packet names the checked hard-wall route surfaces created after
-- 3ce9beb5.  It is deliberately import-light and fail-closed: the packet
-- records the current dependency ladder and the unresolved analytic gates,
-- but it does not promote KornLevelSet, collapseImpossible, or Clay.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSClayHardWallRouteSurface : Set where
  kornConditionalLevelSetTheorem :
    NSClayHardWallRouteSurface
  kornOmegaControlFromPressurePoisson :
    NSClayHardWallRouteSurface
  collapseEigenframeRatioDerivative :
    NSClayHardWallRouteSurface
  collapseBoundaryEnergyQGronwall :
    NSClayHardWallRouteSurface
  collapseBoundarySobolevLift :
    NSClayHardWallRouteSurface
  hardWallCompletionRoadmap :
    NSClayHardWallRouteSurface

canonicalNSClayHardWallRouteSurfaces :
  List NSClayHardWallRouteSurface
canonicalNSClayHardWallRouteSurfaces =
  kornConditionalLevelSetTheorem
  ∷ kornOmegaControlFromPressurePoisson
  ∷ collapseEigenframeRatioDerivative
  ∷ collapseBoundaryEnergyQGronwall
  ∷ collapseBoundarySobolevLift
  ∷ hardWallCompletionRoadmap
  ∷ []

surfaceLabel : NSClayHardWallRouteSurface → String
surfaceLabel kornConditionalLevelSetTheorem =
  "NSKornConditionalLevelSetTheoremReceipt"
surfaceLabel kornOmegaControlFromPressurePoisson =
  "NSKornOmegaControlFromPressurePoissonReceipt"
surfaceLabel collapseEigenframeRatioDerivative =
  "NSCollapseEigenframeRatioDerivativeReceipt"
surfaceLabel collapseBoundaryEnergyQGronwall =
  "NSCollapseBoundaryEnergyQGronwallReceipt"
surfaceLabel collapseBoundarySobolevLift =
  "NSCollapseBoundarySobolevLiftReceipt"
surfaceLabel hardWallCompletionRoadmap =
  "NSClayHardWallCompletionRoadmapReceipt"

canonicalNSClayHardWallRouteSurfaceLabels : List String
canonicalNSClayHardWallRouteSurfaceLabels =
  "NSKornConditionalLevelSetTheoremReceipt"
  ∷ "NSKornOmegaControlFromPressurePoissonReceipt"
  ∷ "NSCollapseEigenframeRatioDerivativeReceipt"
  ∷ "NSCollapseBoundaryEnergyQGronwallReceipt"
  ∷ "NSCollapseBoundarySobolevLiftReceipt"
  ∷ "NSClayHardWallCompletionRoadmapReceipt"
  ∷ []

data NSClayHardWallRouteGate : Set where
  conditionalKornPacketChecked :
    NSClayHardWallRouteGate
  hOmegaCtrlStillOpen :
    NSClayHardWallRouteGate
  collapseDerivativePacketChecked :
    NSClayHardWallRouteGate
  qGronwallStillOpen :
    NSClayHardWallRouteGate
  boundarySobolevLiftPacketChecked :
    NSClayHardWallRouteGate
  collapseImpossibleStillOpen :
    NSClayHardWallRouteGate
  clayPromotionStillFalse :
    NSClayHardWallRouteGate

canonicalNSClayHardWallRouteGates : List NSClayHardWallRouteGate
canonicalNSClayHardWallRouteGates =
  conditionalKornPacketChecked
  ∷ hOmegaCtrlStillOpen
  ∷ collapseDerivativePacketChecked
  ∷ qGronwallStillOpen
  ∷ boundarySobolevLiftPacketChecked
  ∷ collapseImpossibleStillOpen
  ∷ clayPromotionStillFalse
  ∷ []

gateLabel : NSClayHardWallRouteGate → String
gateLabel conditionalKornPacketChecked =
  "conditional KornLevelSet packet checked"
gateLabel hOmegaCtrlStillOpen =
  "h_omega_ctrl from NS alone still open"
gateLabel collapseDerivativePacketChecked =
  "collapse ratio derivative packet checked"
gateLabel qGronwallStillOpen =
  "Q(t) Gronwall estimate still open"
gateLabel boundarySobolevLiftPacketChecked =
  "boundary Sobolev lift packet checked"
gateLabel collapseImpossibleStillOpen =
  "collapseImpossible still open"
gateLabel clayPromotionStillFalse =
  "Clay promotion still false"

canonicalNSClayHardWallRouteGateLabels : List String
canonicalNSClayHardWallRouteGateLabels =
  "conditional KornLevelSet packet checked"
  ∷ "h_omega_ctrl from NS alone still open"
  ∷ "collapse ratio derivative packet checked"
  ∷ "Q(t) Gronwall estimate still open"
  ∷ "boundary Sobolev lift packet checked"
  ∷ "collapseImpossible still open"
  ∷ "Clay promotion still false"
  ∷ []

hardWallRoutePacketStatement : String
hardWallRoutePacketStatement =
  "The current hard-wall route packet decomposes KornLevelSet into a checked conditional packet plus an open h_omega_ctrl-from-NS route, and decomposes collapseImpossible into checked derivative, Q(t)-Gronwall, and boundary-Sobolev-lift packets with the Gronwall/absorption estimates still open."

hardWallRoutePacketBoundary : List String
hardWallRoutePacketBoundary =
  "closeable packages are strengthened at 3ce9beb5"
  ∷ "conditional KornLevelSet packet is checked but not unconditional"
  ∷ "h_omega_ctrl from NS alone remains open"
  ∷ "collapse ratio derivative packet is checked"
  ∷ "Q(t) Gronwall estimate remains open"
  ∷ "boundary Sobolev lift packet is checked but conditional on trace/Hs gates"
  ∷ "collapseImpossible remains open"
  ∷ "Clay promotion remains false"
  ∷ []

record NSClayHardWallRoutePacketReceipt : Setω where
  field
    referenceCommit :
      String
    referenceCommitIsCanonical :
      referenceCommit ≡ "3ce9beb5"

    routeSurfaces :
      List NSClayHardWallRouteSurface
    routeSurfacesAreCanonical :
      routeSurfaces ≡ canonicalNSClayHardWallRouteSurfaces

    routeSurfaceLabels :
      List String
    routeSurfaceLabelsAreCanonical :
      routeSurfaceLabels ≡ canonicalNSClayHardWallRouteSurfaceLabels

    routeSurfaceCount :
      Nat
    routeSurfaceCountIsSix :
      routeSurfaceCount ≡ 6

    routeGates :
      List NSClayHardWallRouteGate
    routeGatesAreCanonical :
      routeGates ≡ canonicalNSClayHardWallRouteGates

    routeGateLabels :
      List String
    routeGateLabelsAreCanonical :
      routeGateLabels ≡ canonicalNSClayHardWallRouteGateLabels

    routeGateCount :
      Nat
    routeGateCountIsSeven :
      routeGateCount ≡ 7

    statement :
      String
    statementIsCanonical :
      statement ≡ hardWallRoutePacketStatement

    kornLevelSetUnconditionalPromoted :
      Bool
    kornLevelSetUnconditionalPromotedIsFalse :
      kornLevelSetUnconditionalPromoted ≡ false

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
      receiptBoundary ≡ hardWallRoutePacketBoundary

open NSClayHardWallRoutePacketReceipt public

canonicalNSClayHardWallRoutePacketReceipt :
  NSClayHardWallRoutePacketReceipt
canonicalNSClayHardWallRoutePacketReceipt =
  record
    { referenceCommit =
        "3ce9beb5"
    ; referenceCommitIsCanonical =
        refl
    ; routeSurfaces =
        canonicalNSClayHardWallRouteSurfaces
    ; routeSurfacesAreCanonical =
        refl
    ; routeSurfaceLabels =
        canonicalNSClayHardWallRouteSurfaceLabels
    ; routeSurfaceLabelsAreCanonical =
        refl
    ; routeSurfaceCount =
        listLength canonicalNSClayHardWallRouteSurfaces
    ; routeSurfaceCountIsSix =
        refl
    ; routeGates =
        canonicalNSClayHardWallRouteGates
    ; routeGatesAreCanonical =
        refl
    ; routeGateLabels =
        canonicalNSClayHardWallRouteGateLabels
    ; routeGateLabelsAreCanonical =
        refl
    ; routeGateCount =
        listLength canonicalNSClayHardWallRouteGates
    ; routeGateCountIsSeven =
        refl
    ; statement =
        hardWallRoutePacketStatement
    ; statementIsCanonical =
        refl
    ; kornLevelSetUnconditionalPromoted =
        false
    ; kornLevelSetUnconditionalPromotedIsFalse =
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
        hardWallRoutePacketBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

routePacketSurfaceCountIsSix :
  routeSurfaceCount canonicalNSClayHardWallRoutePacketReceipt ≡ 6
routePacketSurfaceCountIsSix =
  refl

routePacketGateCountIsSeven :
  routeGateCount canonicalNSClayHardWallRoutePacketReceipt ≡ 7
routePacketGateCountIsSeven =
  refl

routePacketKornLevelSetUnconditionalPromotedIsFalse :
  kornLevelSetUnconditionalPromoted
    canonicalNSClayHardWallRoutePacketReceipt
  ≡ false
routePacketKornLevelSetUnconditionalPromotedIsFalse =
  refl

routePacketCollapseImpossiblePromotedIsFalse :
  collapseImpossiblePromoted canonicalNSClayHardWallRoutePacketReceipt
  ≡ false
routePacketCollapseImpossiblePromotedIsFalse =
  refl

routePacketClayPromotedIsFalse :
  clayPromoted canonicalNSClayHardWallRoutePacketReceipt ≡ false
routePacketClayPromotedIsFalse =
  refl
