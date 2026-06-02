module DASHI.Physics.Closure.MarginInvariantProgrammeFrontierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.KPUniformVolumeBoundReceipt as KPBound
import DASHI.Physics.Closure.NSToEV5ProjectionFrontierReceipt as NSFrontier
import DASHI.Physics.Closure.OverlapDominationLemmaReceipt as Overlap
import DASHI.Physics.Closure.RGContractionExplicitReceipt as RGBridge

------------------------------------------------------------------------
-- Margin-invariant programme frontier receipt.
--
-- This receipt records the updated NS/YM frontier without promoting either
-- Clay lane.  The repo has carrier-side surfaces for NS-to-EV5, KP overlap
-- bookkeeping, and explicit RG operator targets.  The missing bridges remain
-- the analytic margin/contraction proofs that would turn those surfaces into
-- forward simulations or continuum Yang-Mills control.

data MarginInvariantProgrammeFrontierStatus : Set where
  marginInvariantFrontierRecordedNoPromotion :
    MarginInvariantProgrammeFrontierStatus

data FrontierPriority : Set where
  nsRecordThetaTailMarginLessThanOneContinuationProxy :
    FrontierPriority

  ymRecordRhoKPLessThanOneConditionalKPMargin :
    FrontierPriority

  gate3SharedLiftRemainsShared :
    FrontierPriority

canonicalFrontierPriorities : List FrontierPriority
canonicalFrontierPriorities =
  nsRecordThetaTailMarginLessThanOneContinuationProxy
  ∷ ymRecordRhoKPLessThanOneConditionalKPMargin
  ∷ gate3SharedLiftRemainsShared
  ∷ []

data ExistingRepoPiece : Set where
  nsEV5CarrierShapeReceiptExists :
    ExistingRepoPiece

  kpBalabanOverlapCarrierReceiptExists :
    ExistingRepoPiece

  explicitRGOperatorTargetReceiptExists :
    ExistingRepoPiece

canonicalExistingRepoPieces : List ExistingRepoPiece
canonicalExistingRepoPieces =
  nsEV5CarrierShapeReceiptExists
  ∷ kpBalabanOverlapCarrierReceiptExists
  ∷ explicitRGOperatorTargetReceiptExists
  ∷ []

data MissingBridge : Set where
  missingThetaTailMarginLessThanOneProof :
    MissingBridge

  missingNSForwardSimulation :
    MissingBridge

  missingBKMEequivalence :
    MissingBridge

  missingRhoKPLessThanOneProof :
    MissingBridge

  missingKPBalabanContinuumOverlapBridge :
    MissingBridge

  missingRGContractionBridge :
    MissingBridge

  missingGate3SharedLift :
    MissingBridge

canonicalMissingBridges : List MissingBridge
canonicalMissingBridges =
  missingThetaTailMarginLessThanOneProof
  ∷ missingNSForwardSimulation
  ∷ missingBKMEequivalence
  ∷ missingRhoKPLessThanOneProof
  ∷ missingKPBalabanContinuumOverlapBridge
  ∷ missingRGContractionBridge
  ∷ missingGate3SharedLift
  ∷ []

data MarginInvariantProgrammeFrontierPromotion : Set where

marginInvariantProgrammeFrontierPromotionImpossibleHere :
  MarginInvariantProgrammeFrontierPromotion →
  ⊥
marginInvariantProgrammeFrontierPromotionImpossibleHere ()

nsPriorityStatement : String
nsPriorityStatement =
  "NS priority: thetaTailMargin<1 is a sufficient proxy / continuation route marker; forward simulation and BKM equivalence remain open."

ymPriorityStatement : String
ymPriorityStatement =
  "YM priority: rhoKP<1 is a conditional KP margin; KP-Balaban overlap, RG promotion, and Gate3 remain open."

gate3PriorityStatement : String
gate3PriorityStatement =
  "Gate3 remains the shared lift: it is required by both lanes but is not promoted here."

frontierSummaryStatement : String
frontierSummaryStatement =
  "New frontier: theta and rho are seam-gauge margin variables, not proofs; NS theta<1 is a sufficient continuation proxy with BKM equivalence open; YM rhoKP<1 is a conditional KP margin with RG promotion and Gate3 open; all promotion gates remain false."

record MarginInvariantProgrammeFrontierReceipt : Setω where
  field
    status :
      MarginInvariantProgrammeFrontierStatus

    statusIsRecordedNoPromotion :
      status ≡ marginInvariantFrontierRecordedNoPromotion

    priorities :
      List FrontierPriority

    prioritiesAreCanonical :
      priorities ≡ canonicalFrontierPriorities

    existingRepoPieces :
      List ExistingRepoPiece

    existingRepoPiecesAreCanonical :
      existingRepoPieces ≡ canonicalExistingRepoPieces

    missingBridges :
      List MissingBridge

    missingBridgesAreCanonical :
      missingBridges ≡ canonicalMissingBridges

    nsFrontierReceipt :
      NSFrontier.NSToEV5ProjectionFrontierReceipt

    nsCarrierSideShapeClosed :
      NSFrontier.carrierSideEV5FractranCOLShapeClosed nsFrontierReceipt
      ≡
      true

    nsForwardSimulationStillOpen :
      NSFrontier.forwardSimulationProvedHere nsFrontierReceipt
      ≡
      false

    thetaTailMarginLessThanOneProved :
      Bool

    thetaTailMarginLessThanOneProvedIsFalse :
      thetaTailMarginLessThanOneProved ≡ false

    nsForwardSimulationProved :
      Bool

    nsForwardSimulationProvedIsFalse :
      nsForwardSimulationProved ≡ false

    bkmEquivalenceProved :
      Bool

    bkmEquivalenceProvedIsFalse :
      bkmEquivalenceProved ≡ false

    nsClayPromoted :
      Bool

    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false

    kpOverlapReceipt :
      Overlap.OverlapDominationLemmaReceipt

    kpOverlapCarrierBookkeepingRecorded :
      Overlap.kpUniformityFiniteCarrierRecorded kpOverlapReceipt
      ≡
      true

    kpOverlapContinuumStillOpen :
      Overlap.continuumKPProved kpOverlapReceipt
      ≡
      false

    kpUniformVolumeReceipt :
      KPBound.KPUniformVolumeBoundReceipt

    kpBalabanOverlapCarrierBoundRecorded :
      KPBound.carrierSideBoundedObjectRecorded kpUniformVolumeReceipt
      ≡
      true

    kpBalabanContinuumStillOpen :
      KPBound.continuumKPProved kpUniformVolumeReceipt
      ≡
      false

    rgBridgeReceipt :
      RGBridge.RGContractionExplicitReceipt

    rgOperatorTargetRecorded :
      RGBridge.operatorFormulaRecorded rgBridgeReceipt
      ≡
      true

    rgContractionStillOpen :
      RGBridge.rgMapContractionProvedHere rgBridgeReceipt
      ≡
      false

    rhoKPLessThanOneProved :
      Bool

    rhoKPLessThanOneProvedIsFalse :
      rhoKPLessThanOneProved ≡ false

    kpBalabanOverlapBridgeProved :
      Bool

    kpBalabanOverlapBridgeProvedIsFalse :
      kpBalabanOverlapBridgeProved ≡ false

    rgBridgeClosed :
      Bool

    rgBridgeClosedIsFalse :
      rgBridgeClosed ≡ false

    rgPromotionClosed :
      Bool

    rgPromotionClosedIsFalse :
      rgPromotionClosed ≡ false

    ymClayPromoted :
      Bool

    ymClayPromotedIsFalse :
      ymClayPromoted ≡ false

    gate3SharedLiftRequired :
      Bool

    gate3SharedLiftRequiredIsTrue :
      gate3SharedLiftRequired ≡ true

    gate3SharedLiftClosed :
      Bool

    gate3SharedLiftClosedIsFalse :
      gate3SharedLiftClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayPromoted :
      Bool

    terminalClayPromotedIsFalse :
      terminalClayPromoted ≡ false

    promotionFlags :
      List MarginInvariantProgrammeFrontierPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    nsPriority :
      String

    nsPriorityIsCanonical :
      nsPriority ≡ nsPriorityStatement

    ymPriority :
      String

    ymPriorityIsCanonical :
      ymPriority ≡ ymPriorityStatement

    gate3Priority :
      String

    gate3PriorityIsCanonical :
      gate3Priority ≡ gate3PriorityStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ frontierSummaryStatement

    receiptBoundary :
      List String

open MarginInvariantProgrammeFrontierReceipt public

canonicalMarginInvariantProgrammeFrontierReceipt :
  MarginInvariantProgrammeFrontierReceipt
canonicalMarginInvariantProgrammeFrontierReceipt =
  record
    { status =
        marginInvariantFrontierRecordedNoPromotion
    ; statusIsRecordedNoPromotion =
        refl
    ; priorities =
        canonicalFrontierPriorities
    ; prioritiesAreCanonical =
        refl
    ; existingRepoPieces =
        canonicalExistingRepoPieces
    ; existingRepoPiecesAreCanonical =
        refl
    ; missingBridges =
        canonicalMissingBridges
    ; missingBridgesAreCanonical =
        refl
    ; nsFrontierReceipt =
        NSFrontier.canonicalNSToEV5ProjectionFrontierReceipt
    ; nsCarrierSideShapeClosed =
        refl
    ; nsForwardSimulationStillOpen =
        refl
    ; thetaTailMarginLessThanOneProved =
        false
    ; thetaTailMarginLessThanOneProvedIsFalse =
        refl
    ; nsForwardSimulationProved =
        false
    ; nsForwardSimulationProvedIsFalse =
        refl
    ; bkmEquivalenceProved =
        false
    ; bkmEquivalenceProvedIsFalse =
        refl
    ; nsClayPromoted =
        false
    ; nsClayPromotedIsFalse =
        refl
    ; kpOverlapReceipt =
        Overlap.canonicalOverlapDominationLemmaReceipt
    ; kpOverlapCarrierBookkeepingRecorded =
        refl
    ; kpOverlapContinuumStillOpen =
        refl
    ; kpUniformVolumeReceipt =
        KPBound.canonicalKPUniformVolumeBoundReceipt
    ; kpBalabanOverlapCarrierBoundRecorded =
        refl
    ; kpBalabanContinuumStillOpen =
        refl
    ; rgBridgeReceipt =
        RGBridge.canonicalRGContractionExplicitReceipt
    ; rgOperatorTargetRecorded =
        refl
    ; rgContractionStillOpen =
        refl
    ; rhoKPLessThanOneProved =
        false
    ; rhoKPLessThanOneProvedIsFalse =
        refl
    ; kpBalabanOverlapBridgeProved =
        false
    ; kpBalabanOverlapBridgeProvedIsFalse =
        refl
    ; rgBridgeClosed =
        false
    ; rgBridgeClosedIsFalse =
        refl
    ; rgPromotionClosed =
        false
    ; rgPromotionClosedIsFalse =
        refl
    ; ymClayPromoted =
        false
    ; ymClayPromotedIsFalse =
        refl
    ; gate3SharedLiftRequired =
        true
    ; gate3SharedLiftRequiredIsTrue =
        refl
    ; gate3SharedLiftClosed =
        false
    ; gate3SharedLiftClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayPromoted =
        false
    ; terminalClayPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; nsPriority =
        nsPriorityStatement
    ; nsPriorityIsCanonical =
        refl
    ; ymPriority =
        ymPriorityStatement
    ; ymPriorityIsCanonical =
        refl
    ; gate3Priority =
        gate3PriorityStatement
    ; gate3PriorityIsCanonical =
        refl
    ; statement =
        frontierSummaryStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Records theta and rho as seam-gauge margin variables, not proofs"
        ∷ "Records the NS side as thetaTailMargin<1 sufficient proxy / continuation route, with forward simulation and BKM equivalence open"
        ∷ "Consumes the existing NS-to-EV5 carrier-shape receipt while keeping forward simulation false"
        ∷ "Records the YM side as rhoKP<1 conditional KP margin, with KP-Balaban overlap, RG promotion, and Gate3 open"
        ∷ "Consumes existing KP overlap, KP uniform-volume, and explicit RG target receipts while keeping continuum KP and RG contraction false"
        ∷ "Gate3 remains the shared lift and is not closed by this receipt"
        ∷ "Repo pieces exist, bridges are missing, and all promotion gates remain false"
        ∷ []
    }

canonicalFrontierKeepsThetaTailMarginOpen :
  thetaTailMarginLessThanOneProved
    canonicalMarginInvariantProgrammeFrontierReceipt
  ≡
  false
canonicalFrontierKeepsThetaTailMarginOpen =
  refl

canonicalFrontierKeepsRhoKPOpen :
  rhoKPLessThanOneProved canonicalMarginInvariantProgrammeFrontierReceipt
  ≡
  false
canonicalFrontierKeepsRhoKPOpen =
  refl

canonicalFrontierKeepsGate3SharedLiftOpen :
  gate3SharedLiftClosed canonicalMarginInvariantProgrammeFrontierReceipt
  ≡
  false
canonicalFrontierKeepsGate3SharedLiftOpen =
  refl

canonicalFrontierKeepsBKMEquivalenceOpen :
  bkmEquivalenceProved canonicalMarginInvariantProgrammeFrontierReceipt
  ≡
  false
canonicalFrontierKeepsBKMEquivalenceOpen =
  refl

canonicalFrontierKeepsRGPromotionOpen :
  rgPromotionClosed canonicalMarginInvariantProgrammeFrontierReceipt
  ≡
  false
canonicalFrontierKeepsRGPromotionOpen =
  refl

canonicalFrontierNoPromotion :
  MarginInvariantProgrammeFrontierPromotion →
  ⊥
canonicalFrontierNoPromotion =
  marginInvariantProgrammeFrontierPromotionImpossibleHere
