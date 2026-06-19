module DASHI.Physics.Closure.NSCollapseConditionalGronwallBridgeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSCollapseBoundaryEnergyQGronwallReceipt
  as QRoute
import DASHI.Physics.Closure.NSCollapseRatioAbsorptionCriterionReceipt
  as RatioRoute
import DASHI.Physics.Closure.NSBoundaryLambda3F123EmpiricalReceipt
  as EmpiricalRoute
import DASHI.Physics.Closure.NSCollapseF123SingularAbsorptionClosureReceipt
  as F123Route
import DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt
  as TheoremG

------------------------------------------------------------------------
-- Fail-closed bridge receipt for the conditional Gronwall route.
--
-- This module only records the checked bridge surface:
--   h_delta1 + TheoremG -> collapseImpossible_conditional
-- and explicitly does not claim the unconditional collapseImpossible
-- theorem.  The conditional Theorem G receipt is imported as a dependency,
-- while all unconditional promotion flags remain false.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSCollapseConditionalGronwallBridgeStatus : Set where
  conditionalBridgeReceiptRecorded :
    NSCollapseConditionalGronwallBridgeStatus

data NSCollapseConditionalGronwallBridgeBlocker : Set where
  NoLambda3CollapseOnKatoCarrier :
    NSCollapseConditionalGronwallBridgeBlocker
  LayerKornInequality :
    NSCollapseConditionalGronwallBridgeBlocker
  RellichKatoCommutatorProofTerm :
    NSCollapseConditionalGronwallBridgeBlocker
  LayerCZ :
    NSCollapseConditionalGronwallBridgeBlocker

canonicalNSCollapseConditionalGronwallBridgeBlockers :
  List NSCollapseConditionalGronwallBridgeBlocker
canonicalNSCollapseConditionalGronwallBridgeBlockers =
  NoLambda3CollapseOnKatoCarrier
  ∷ LayerKornInequality
  ∷ RellichKatoCommutatorProofTerm
  ∷ LayerCZ
  ∷ []

canonicalNSCollapseConditionalGronwallDependencyNames :
  List String
canonicalNSCollapseConditionalGronwallDependencyNames =
  "DASHI.Physics.Closure.NSCollapseBoundaryEnergyQGronwallReceipt"
  ∷ "DASHI.Physics.Closure.NSCollapseRatioAbsorptionCriterionReceipt"
  ∷ "DASHI.Physics.Closure.NSBoundaryLambda3F123EmpiricalReceipt"
  ∷ "DASHI.Physics.Closure.NSCollapseF123SingularAbsorptionClosureReceipt"
  ∷ "DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt"
  ∷ "h_delta1"
  ∷ "TheoremG"
  ∷ "collapseImpossible_conditional"
  ∷ []

conditionalRouteText : String
conditionalRouteText =
  "h_delta1 + TheoremG -> collapseImpossible_conditional only; the unconditional collapseImpossible theorem is not claimed."

theoremGSurfaceImportedText : String
theoremGSurfaceImportedText =
  "The conditional Theorem G receipt is imported and visible, but it is conditional only and does not discharge h_delta1."

receiptBoundaryText : List String
receiptBoundaryText =
  "This bridge connects the Q(t) boundary-energy route to the ratio, empirical, and singular F123 receipts"
  ∷ "The current repo records a conditional route only: h_delta1 + TheoremG -> collapseImpossible_conditional"
  ∷ "The unconditional collapseImpossible theorem is explicitly not claimed"
  ∷ "The conditional Theorem G receipt is imported and visible"
  ∷ "Blockers are recorded as NoLambda3CollapseOnKatoCarrier, LayerKornInequality, RellichKatoCommutatorProofTerm, and LayerCZ"
  ∷ "collapseImpossible, hDelta1Discharged, and clayNavierStokesPromoted remain false"
  ∷ []

record NSCollapseConditionalGronwallBridgeReceipt : Setω where
  field
    status :
      NSCollapseConditionalGronwallBridgeStatus
    statusIsCanonical :
      status ≡ conditionalBridgeReceiptRecorded

    qBoundaryEnergyReceiptImported :
      Bool
    qBoundaryEnergyReceiptImportedIsTrue :
      qBoundaryEnergyReceiptImported ≡ true

    ratioAbsorptionReceiptImported :
      Bool
    ratioAbsorptionReceiptImportedIsTrue :
      ratioAbsorptionReceiptImported ≡ true

    empiricalBoundaryReceiptImported :
      Bool
    empiricalBoundaryReceiptImportedIsTrue :
      empiricalBoundaryReceiptImported ≡ true

    singularAbsorptionReceiptImported :
      Bool
    singularAbsorptionReceiptImportedIsTrue :
      singularAbsorptionReceiptImported ≡ true

    theoremGReceiptImported :
      Bool
    theoremGReceiptImportedIsTrue :
      theoremGReceiptImported ≡ true

    dependencyNames :
      List String
    dependencyNamesIsCanonical :
      dependencyNames
      ≡ canonicalNSCollapseConditionalGronwallDependencyNames

    dependencyNameCount :
      Nat
    dependencyNameCountIsCanonical :
      dependencyNameCount
      ≡ listLength canonicalNSCollapseConditionalGronwallDependencyNames

    blockers :
      List NSCollapseConditionalGronwallBridgeBlocker
    blockersIsCanonical :
      blockers ≡ canonicalNSCollapseConditionalGronwallBridgeBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount
      ≡ listLength canonicalNSCollapseConditionalGronwallBridgeBlockers

    conditionalRoute :
      String
    conditionalRouteIsCanonical :
      conditionalRoute ≡ conditionalRouteText

    theoremGSurfaceImported :
      String
    theoremGSurfaceImportedIsCanonical :
      theoremGSurfaceImported ≡ theoremGSurfaceImportedText

    collapseImpossible_conditional :
      Bool
    collapseImpossible_conditionalIsTrue :
      collapseImpossible_conditional ≡ true

    theoremSurfaceVisible :
      Bool
    theoremSurfaceVisibleIsTrue :
      theoremSurfaceVisible ≡ true

    collapseImpossible :
      Bool
    collapseImpossibleIsFalse :
      collapseImpossible ≡ false

    hDelta1Discharged :
      Bool
    hDelta1DischargedIsFalse :
      hDelta1Discharged ≡ false

    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

open NSCollapseConditionalGronwallBridgeReceipt public

canonicalNSCollapseConditionalGronwallBridgeReceipt :
  NSCollapseConditionalGronwallBridgeReceipt
canonicalNSCollapseConditionalGronwallBridgeReceipt =
  record
    { status =
        conditionalBridgeReceiptRecorded
    ; statusIsCanonical =
        refl
    ; qBoundaryEnergyReceiptImported =
        true
    ; qBoundaryEnergyReceiptImportedIsTrue =
        refl
    ; ratioAbsorptionReceiptImported =
        true
    ; ratioAbsorptionReceiptImportedIsTrue =
        refl
    ; empiricalBoundaryReceiptImported =
        true
    ; empiricalBoundaryReceiptImportedIsTrue =
        refl
    ; singularAbsorptionReceiptImported =
        true
    ; singularAbsorptionReceiptImportedIsTrue =
        refl
    ; theoremGReceiptImported =
        true
    ; theoremGReceiptImportedIsTrue =
        refl
    ; dependencyNames =
        canonicalNSCollapseConditionalGronwallDependencyNames
    ; dependencyNamesIsCanonical =
        refl
    ; dependencyNameCount =
        listLength canonicalNSCollapseConditionalGronwallDependencyNames
    ; dependencyNameCountIsCanonical =
        refl
    ; blockers =
        canonicalNSCollapseConditionalGronwallBridgeBlockers
    ; blockersIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSCollapseConditionalGronwallBridgeBlockers
    ; blockerCountIsCanonical =
        refl
    ; conditionalRoute =
        conditionalRouteText
    ; conditionalRouteIsCanonical =
        refl
    ; theoremGSurfaceImported =
        theoremGSurfaceImportedText
    ; theoremGSurfaceImportedIsCanonical =
        refl
    ; collapseImpossible_conditional =
        true
    ; collapseImpossible_conditionalIsTrue =
        refl
    ; theoremSurfaceVisible =
        true
    ; theoremSurfaceVisibleIsTrue =
        refl
    ; collapseImpossible =
        false
    ; collapseImpossibleIsFalse =
        refl
    ; hDelta1Discharged =
        false
    ; hDelta1DischargedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

bridgeKeepsCollapseImpossibleFalse :
  collapseImpossible canonicalNSCollapseConditionalGronwallBridgeReceipt ≡ false
bridgeKeepsCollapseImpossibleFalse =
  refl

bridgeKeepsHDelta1DischargedFalse :
  hDelta1Discharged canonicalNSCollapseConditionalGronwallBridgeReceipt ≡ false
bridgeKeepsHDelta1DischargedFalse =
  refl

bridgeKeepsClayNavierStokesPromotedFalse :
  clayNavierStokesPromoted canonicalNSCollapseConditionalGronwallBridgeReceipt ≡ false
bridgeKeepsClayNavierStokesPromotedFalse =
  refl

bridgeRecordsConditionalRouteOnly :
  collapseImpossible_conditional canonicalNSCollapseConditionalGronwallBridgeReceipt ≡ true
bridgeRecordsConditionalRouteOnly =
  refl
