module DASHI.Physics.Closure.DangerScaleEdgeConservationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierMoscoConvergenceFromPhysicsReceipt
  as Gate3Mosco
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as NSMargin
import DASHI.Physics.Closure.NSTailFluxIdentityAnalyticTargetReceipt
  as NSIdentity
import DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt
  as YMActual
import DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt
  as YMRG
import DASHI.Physics.Closure.YMKPActivityRatioMarginReceipt as YMRho

------------------------------------------------------------------------
-- Danger-scale edge conservation receipt.
--
-- The scale-graph maximum-principle shape needs one load-bearing hypothesis:
-- activity cannot enter the current danger node from nowhere.  Every
-- lane must discharge a controlled edge-transfer law before the universal
-- barrier may be consumed.
--
-- This receipt records that hypothesis and the three concrete lane
-- instantiations.  It does not prove any lane edge law, does not prove the
-- maximum principle, and keeps Clay/publication promotion fail-closed even
-- though the repo-internal NS/YM/Gate 3 closure surfaces are already
-- recorded upstream.

data DangerScaleEdgeStatus : Set where
  dangerScaleEdgeConservationRecorded_failClosed :
    DangerScaleEdgeStatus

data ScaleEdgeLaw : Set where
  adjacentNodeTransferOnly :
    ScaleEdgeLaw

  noHiddenProductionAtDangerNode :
    ScaleEdgeLaw

  leakageBoundedByExplicitEpsilon :
    ScaleEdgeLaw

  leakageStrictlyBelowAbsorptionSlope :
    ScaleEdgeLaw

canonicalScaleEdgeLaws : List ScaleEdgeLaw
canonicalScaleEdgeLaws =
  adjacentNodeTransferOnly
  ∷ noHiddenProductionAtDangerNode
  ∷ leakageBoundedByExplicitEpsilon
  ∷ leakageStrictlyBelowAbsorptionSlope
  ∷ []

data EdgeConservationLane : Set where
  nsAdjacentShellFluxLane :
    EdgeConservationLane

  ymBlockSpinRGLane :
    EdgeConservationLane

  gate3RefinementCutoffLane :
    EdgeConservationLane

canonicalEdgeConservationLanes : List EdgeConservationLane
canonicalEdgeConservationLanes =
  nsAdjacentShellFluxLane
  ∷ ymBlockSpinRGLane
  ∷ gate3RefinementCutoffLane
  ∷ []

data LaneEdgeTransfer : Set where
  nsLittlewoodPaleyAdjacentShellTransfer :
    LaneEdgeTransfer

  ymBalabanBlockSpinActivityTransfer :
    LaneEdgeTransfer

  gate3MoscoRefinementDefectTransfer :
    LaneEdgeTransfer

canonicalLaneEdgeTransfer : EdgeConservationLane → LaneEdgeTransfer
canonicalLaneEdgeTransfer nsAdjacentShellFluxLane =
  nsLittlewoodPaleyAdjacentShellTransfer
canonicalLaneEdgeTransfer ymBlockSpinRGLane =
  ymBalabanBlockSpinActivityTransfer
canonicalLaneEdgeTransfer gate3RefinementCutoffLane =
  gate3MoscoRefinementDefectTransfer

data EdgeConservationObligation : Set where
  proveNSTailFluxTransfersOnlyAcrossAdjacentShells :
    EdgeConservationObligation

  proveNSDangerShellReceivesNoUntrackedHighHighSource :
    EdgeConservationObligation

  proveYMActualRhoBlockSpinRecurrence :
    EdgeConservationObligation

  proveYMRGLeakageTermSummable :
    EdgeConservationObligation

  proveGate3RefinementDefectAccounting :
    EdgeConservationObligation

  proveGate3MoscoTailCannotInjectHiddenDefect :
    EdgeConservationObligation

canonicalEdgeConservationObligations :
  List EdgeConservationObligation
canonicalEdgeConservationObligations =
  proveNSTailFluxTransfersOnlyAcrossAdjacentShells
  ∷ proveNSDangerShellReceivesNoUntrackedHighHighSource
  ∷ proveYMActualRhoBlockSpinRecurrence
  ∷ proveYMRGLeakageTermSummable
  ∷ proveGate3RefinementDefectAccounting
  ∷ proveGate3MoscoTailCannotInjectHiddenDefect
  ∷ []

data EdgeConservationBoundary : Set where
  edgeLawRequiredBeforeBarrierConsumption :
    EdgeConservationBoundary

  diagnosticsDoNotSupplyEdgeLaw :
    EdgeConservationBoundary

  toyRhoDoesNotSupplyEdgeLaw :
    EdgeConservationBoundary

  physicalMoscoIntuitionDoesNotSupplyEdgeLaw :
    EdgeConservationBoundary

  noLaneClosureFromThisReceipt :
    EdgeConservationBoundary

canonicalEdgeConservationBoundaries :
  List EdgeConservationBoundary
canonicalEdgeConservationBoundaries =
  edgeLawRequiredBeforeBarrierConsumption
  ∷ diagnosticsDoNotSupplyEdgeLaw
  ∷ toyRhoDoesNotSupplyEdgeLaw
  ∷ physicalMoscoIntuitionDoesNotSupplyEdgeLaw
  ∷ noLaneClosureFromThisReceipt
  ∷ []

record EdgeConservationLaneRow : Set where
  field
    lane :
      EdgeConservationLane

    transfer :
      LaneEdgeTransfer

    transferIsCanonical :
      transfer ≡ canonicalLaneEdgeTransfer lane

    edgeLawProved :
      Bool

    edgeLawProvedIsFalse :
      edgeLawProved ≡ false

open EdgeConservationLaneRow public

rowFor : EdgeConservationLane → EdgeConservationLaneRow
rowFor lane =
  record
    { lane =
        lane
    ; transfer =
        canonicalLaneEdgeTransfer lane
    ; transferIsCanonical =
        refl
    ; edgeLawProved =
        false
    ; edgeLawProvedIsFalse =
        refl
    }

canonicalEdgeConservationRows : List EdgeConservationLaneRow
canonicalEdgeConservationRows =
  rowFor nsAdjacentShellFluxLane
  ∷ rowFor ymBlockSpinRGLane
  ∷ rowFor gate3RefinementCutoffLane
  ∷ []

data DangerScaleEdgePromotion : Set where

dangerScaleEdgePromotionImpossibleHere :
  DangerScaleEdgePromotion →
  ⊥
dangerScaleEdgePromotionImpossibleHere ()

edgeConservationStatement : String
edgeConservationStatement =
  "The scale-graph barrier requires controlled edge accounting: what leaves one scale node must enter an adjacent node or be dissipated, with leakage epsilon strictly below the absorber slope; this receipt records that obligation without reopening NS, YM, or Gate 3 closure, and without any Clay promotion."

edgeConservationBoundaryStatement : String
edgeConservationBoundaryStatement =
  "This receipt records the edge-conservation obligation only; it does not prove the NS adjacent-shell law, YM Balaban recurrence, or Gate 3 Mosco refinement law, and it makes no Clay claim."

record DangerScaleEdgeConservationReceipt : Setω where
  field
    status :
      DangerScaleEdgeStatus

    statusIsFailClosed :
      status ≡ dangerScaleEdgeConservationRecorded_failClosed

    nsMarginReceipt :
      NSMargin.NSTailFluxAbsorptionMarginReceipt

    nsMarginNoClay :
      NSMargin.NSTailFluxAbsorptionMarginReceipt.clayNavierStokesPromoted
        nsMarginReceipt
      ≡
      false

    nsIdentityReceipt :
      NSIdentity.NSTailFluxIdentityAnalyticTargetReceipt 0

    nsIdentityStillTarget :
      NSIdentity.lpIdentityProvedHere nsIdentityReceipt ≡ false

    ymRhoReceipt :
      YMRho.YMKPActivityRatioMarginReceipt

    ymToyRhoNotProof :
      YMRho.toyRhoProfilePromotedAsProof ymRhoReceipt ≡ false

    ymActualReceipt :
      YMActual.YMActualPolymerActivityDefinitionReceipt

    ymActualActivityRecorded :
      YMActual.actualPolymerActivitySupplied ymActualReceipt ≡ true

    ymRGReceipt :
      YMRG.YMBalabanRGScaleTransferFrontierReceipt

    ymRGStillMissing :
      YMRG.balabanRGProofPresent ymRGReceipt ≡ false

    gate3MoscoReceipt :
      Gate3Mosco.CarrierMoscoConvergenceFromPhysicsReceipt

    gate3MoscoStillNeedsProof :
      Gate3Mosco.formalProofRequired gate3MoscoReceipt ≡ true

    laws :
      List ScaleEdgeLaw

    lawsAreCanonical :
      laws ≡ canonicalScaleEdgeLaws

    lanes :
      List EdgeConservationLane

    lanesAreCanonical :
      lanes ≡ canonicalEdgeConservationLanes

    laneRows :
      List EdgeConservationLaneRow

    laneRowsAreCanonical :
      laneRows ≡ canonicalEdgeConservationRows

    obligations :
      List EdgeConservationObligation

    obligationsAreCanonical :
      obligations ≡ canonicalEdgeConservationObligations

    boundaries :
      List EdgeConservationBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalEdgeConservationBoundaries

    edgeConservationProvedHere :
      Bool

    edgeConservationProvedHereIsFalse :
      edgeConservationProvedHere ≡ false

    barrierMayConsumeThisAsProof :
      Bool

    barrierMayConsumeThisAsProofIsFalse :
      barrierMayConsumeThisAsProof ≡ false

    nsClosurePromoted :
      Bool

    nsClosurePromotedIsFalse :
      nsClosurePromoted ≡ false

    ymClosurePromoted :
      Bool

    ymClosurePromotedIsFalse :
      ymClosurePromoted ≡ false

    gate3ClosurePromoted :
      Bool

    gate3ClosurePromotedIsFalse :
      gate3ClosurePromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ edgeConservationStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ edgeConservationBoundaryStatement

    promotions :
      List DangerScaleEdgePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      DangerScaleEdgePromotion →
      ⊥

open DangerScaleEdgeConservationReceipt public

canonicalDangerScaleEdgeConservationReceipt :
  DangerScaleEdgeConservationReceipt
canonicalDangerScaleEdgeConservationReceipt =
  record
    { status =
        dangerScaleEdgeConservationRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; nsMarginReceipt =
        NSMargin.canonicalNSTailFluxAbsorptionMarginReceipt
    ; nsMarginNoClay =
        refl
    ; nsIdentityReceipt =
        NSIdentity.canonicalNSTailFluxIdentityAnalyticTargetReceipt
    ; nsIdentityStillTarget =
        refl
    ; ymRhoReceipt =
        YMRho.canonicalYMKPActivityRatioMarginReceipt
    ; ymToyRhoNotProof =
        refl
    ; ymActualReceipt =
        YMActual.canonicalYMActualPolymerActivityDefinitionReceipt
    ; ymActualActivityRecorded =
        refl
    ; ymRGReceipt =
        YMRG.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; ymRGStillMissing =
        refl
    ; gate3MoscoReceipt =
        Gate3Mosco.canonicalCarrierMoscoConvergenceFromPhysicsReceipt
    ; gate3MoscoStillNeedsProof =
        refl
    ; laws =
        canonicalScaleEdgeLaws
    ; lawsAreCanonical =
        refl
    ; lanes =
        canonicalEdgeConservationLanes
    ; lanesAreCanonical =
        refl
    ; laneRows =
        canonicalEdgeConservationRows
    ; laneRowsAreCanonical =
        refl
    ; obligations =
        canonicalEdgeConservationObligations
    ; obligationsAreCanonical =
        refl
    ; boundaries =
        canonicalEdgeConservationBoundaries
    ; boundariesAreCanonical =
        refl
    ; edgeConservationProvedHere =
        false
    ; edgeConservationProvedHereIsFalse =
        refl
    ; barrierMayConsumeThisAsProof =
        false
    ; barrierMayConsumeThisAsProofIsFalse =
        refl
    ; nsClosurePromoted =
        false
    ; nsClosurePromotedIsFalse =
        refl
    ; ymClosurePromoted =
        false
    ; ymClosurePromotedIsFalse =
        refl
    ; gate3ClosurePromoted =
        false
    ; gate3ClosurePromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; statement =
        edgeConservationStatement
    ; statementIsCanonical =
        refl
    ; boundaryStatement =
        edgeConservationBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        dangerScaleEdgePromotionImpossibleHere
    }

canonicalDangerScaleEdgeConservationNoProof :
  edgeConservationProvedHere canonicalDangerScaleEdgeConservationReceipt
    ≡ false
canonicalDangerScaleEdgeConservationNoProof =
  refl

canonicalDangerScaleEdgeConservationNoClay :
  clayPromotion canonicalDangerScaleEdgeConservationReceipt ≡ false
canonicalDangerScaleEdgeConservationNoClay =
  refl
