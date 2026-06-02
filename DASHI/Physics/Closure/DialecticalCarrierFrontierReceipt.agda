module DASHI.Physics.Closure.DialecticalCarrierFrontierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSTailDominanceCarryAnalogyReceipt as NSTailCarry
import DASHI.Physics.Closure.SSPSevenSevenOneAtomFieldReceipt as SSP771

------------------------------------------------------------------------
-- Dialectical carrier frontier receipt.
--
-- This receipt integrates the presently available carrier-frontier batch
-- surfaces and records unavailable siblings as unbound bookkeeping slots.
-- It is a receipt frontier only: no physics theorem, no Gate 3 closure, and
-- no Clay promotion are introduced here.

data DialecticalCarrierFrontierStatus : Set where
  dialecticalCarrierFrontierRecorded_bookkeepingOnly :
    DialecticalCarrierFrontierStatus

data BatchReceiptSlot : Set where
  sevenSevenOneSlot :
    BatchReceiptSlot

  carryProjectionDefectSlot :
    BatchReceiptSlot

  carrierStateVariableMappingSlot :
    BatchReceiptSlot

  activeLanePressureEnergySlot :
    BatchReceiptSlot

  modulusLadderSlot :
    BatchReceiptSlot

  nsTailCarryAnalogySlot :
    BatchReceiptSlot

canonicalBatchReceiptSlots :
  List BatchReceiptSlot
canonicalBatchReceiptSlots =
  sevenSevenOneSlot
  ∷ carryProjectionDefectSlot
  ∷ carrierStateVariableMappingSlot
  ∷ activeLanePressureEnergySlot
  ∷ modulusLadderSlot
  ∷ nsTailCarryAnalogySlot
  ∷ []

data BatchReceiptBinding : Set where
  boundSevenSevenOneReceipt :
    BatchReceiptBinding

  unboundCarryProjectionDefectReceipt :
    BatchReceiptBinding

  unboundCarrierStateVariableMappingReceipt :
    BatchReceiptBinding

  unboundActiveLanePressureEnergyReceipt :
    BatchReceiptBinding

  unboundModulusLadderReceipt :
    BatchReceiptBinding

  boundNSTailCarryAnalogyReceipt :
    BatchReceiptBinding

canonicalBatchReceiptBindings :
  List BatchReceiptBinding
canonicalBatchReceiptBindings =
  boundSevenSevenOneReceipt
  ∷ unboundCarryProjectionDefectReceipt
  ∷ unboundCarrierStateVariableMappingReceipt
  ∷ unboundActiveLanePressureEnergyReceipt
  ∷ unboundModulusLadderReceipt
  ∷ boundNSTailCarryAnalogyReceipt
  ∷ []

data DialecticalCarrierFrontierBoundary : Set where
  bookkeepingOnly :
    DialecticalCarrierFrontierBoundary

  noPhysicsTheorem :
    DialecticalCarrierFrontierBoundary

  noGate3Closure :
    DialecticalCarrierFrontierBoundary

  noClayPromotion :
    DialecticalCarrierFrontierBoundary

canonicalDialecticalCarrierFrontierBoundaries :
  List DialecticalCarrierFrontierBoundary
canonicalDialecticalCarrierFrontierBoundaries =
  bookkeepingOnly
  ∷ noPhysicsTheorem
  ∷ noGate3Closure
  ∷ noClayPromotion
  ∷ []

data DialecticalCarrierFrontierPromotion : Set where

dialecticalCarrierFrontierPromotionImpossibleHere :
  DialecticalCarrierFrontierPromotion →
  ⊥
dialecticalCarrierFrontierPromotionImpossibleHere ()

frontierStatement :
  String
frontierStatement =
  "The dialectical carrier frontier integrates available batch receipts and records missing siblings as unbound bookkeeping slots."

sevenSevenOneStatement :
  String
sevenSevenOneStatement =
  "Seven-seven-one is bound through the existing 15SSP 7+7+1 atom-field receipt."

missingSiblingsStatement :
  String
missingSiblingsStatement =
  "Carry projection-defect, carrier state variable mapping, active-lane pressure energy, and modulus ladder receipts are not imported here because matching sibling receipt modules were not present."

nsTailCarryStatement :
  String
nsTailCarryStatement =
  "NS tail carry analogy is bound through the tail-dominance carry analogy receipt."

boundaryStatement :
  String
boundaryStatement =
  "This frontier is bookkeeping only: no physics theorem, no Gate 3 closure, and no Clay promotion."

record DialecticalCarrierFrontierReceipt : Setω where
  field
    status :
      DialecticalCarrierFrontierStatus

    statusIsBookkeepingOnly :
      status ≡ dialecticalCarrierFrontierRecorded_bookkeepingOnly

    sevenSevenOneReceipt :
      SSP771.SSPSevenSevenOneAtomFieldReceipt

    sevenSevenOneTotalIsFifteen :
      SSP771.totalSSPLaneCount sevenSevenOneReceipt ≡ 15

    nsTailCarryAnalogyReceipt :
      NSTailCarry.NSTailDominanceCarryAnalogyReceipt

    nsTailCarryNoNSProof :
      NSTailCarry.nsProofPromoted nsTailCarryAnalogyReceipt ≡ false

    nsTailCarryNoGate3Closure :
      NSTailCarry.gate3ClosurePromoted nsTailCarryAnalogyReceipt ≡ false

    nsTailCarryNoClayPromotion :
      NSTailCarry.clayPromotionMade nsTailCarryAnalogyReceipt ≡ false

    batchSlots :
      List BatchReceiptSlot

    batchSlotsAreCanonical :
      batchSlots ≡ canonicalBatchReceiptSlots

    batchBindings :
      List BatchReceiptBinding

    batchBindingsAreCanonical :
      batchBindings ≡ canonicalBatchReceiptBindings

    boundReceiptCount :
      Nat

    boundReceiptCountIsTwo :
      boundReceiptCount ≡ 2

    unboundReceiptCount :
      Nat

    unboundReceiptCountIsFour :
      unboundReceiptCount ≡ 4

    frontierSummary :
      String

    frontierSummaryIsCanonical :
      frontierSummary ≡ frontierStatement

    sevenSevenOneSummary :
      String

    sevenSevenOneSummaryIsCanonical :
      sevenSevenOneSummary ≡ sevenSevenOneStatement

    missingSiblingsSummary :
      String

    missingSiblingsSummaryIsCanonical :
      missingSiblingsSummary ≡ missingSiblingsStatement

    nsTailCarrySummary :
      String

    nsTailCarrySummaryIsCanonical :
      nsTailCarrySummary ≡ nsTailCarryStatement

    bookkeepingOnlyFlag :
      Bool

    bookkeepingOnlyFlagIsTrue :
      bookkeepingOnlyFlag ≡ true

    physicsTheoremPromoted :
      Bool

    physicsTheoremPromotedIsFalse :
      physicsTheoremPromoted ≡ false

    gate3ClosurePromoted :
      Bool

    gate3ClosurePromotedIsFalse :
      gate3ClosurePromoted ≡ false

    clayPromotionMade :
      Bool

    clayPromotionMadeIsFalse :
      clayPromotionMade ≡ false

    boundaries :
      List DialecticalCarrierFrontierBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalDialecticalCarrierFrontierBoundaries

    promotionFlags :
      List DialecticalCarrierFrontierPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotion :
      DialecticalCarrierFrontierPromotion →
      ⊥

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

open DialecticalCarrierFrontierReceipt public

canonicalDialecticalCarrierFrontierReceipt :
  DialecticalCarrierFrontierReceipt
canonicalDialecticalCarrierFrontierReceipt =
  record
    { status =
        dialecticalCarrierFrontierRecorded_bookkeepingOnly
    ; statusIsBookkeepingOnly =
        refl
    ; sevenSevenOneReceipt =
        SSP771.canonicalSSPSevenSevenOneAtomFieldReceipt
    ; sevenSevenOneTotalIsFifteen =
        refl
    ; nsTailCarryAnalogyReceipt =
        NSTailCarry.canonicalNSTailDominanceCarryAnalogyReceipt
    ; nsTailCarryNoNSProof =
        refl
    ; nsTailCarryNoGate3Closure =
        refl
    ; nsTailCarryNoClayPromotion =
        refl
    ; batchSlots =
        canonicalBatchReceiptSlots
    ; batchSlotsAreCanonical =
        refl
    ; batchBindings =
        canonicalBatchReceiptBindings
    ; batchBindingsAreCanonical =
        refl
    ; boundReceiptCount =
        2
    ; boundReceiptCountIsTwo =
        refl
    ; unboundReceiptCount =
        4
    ; unboundReceiptCountIsFour =
        refl
    ; frontierSummary =
        frontierStatement
    ; frontierSummaryIsCanonical =
        refl
    ; sevenSevenOneSummary =
        sevenSevenOneStatement
    ; sevenSevenOneSummaryIsCanonical =
        refl
    ; missingSiblingsSummary =
        missingSiblingsStatement
    ; missingSiblingsSummaryIsCanonical =
        refl
    ; nsTailCarrySummary =
        nsTailCarryStatement
    ; nsTailCarrySummaryIsCanonical =
        refl
    ; bookkeepingOnlyFlag =
        true
    ; bookkeepingOnlyFlagIsTrue =
        refl
    ; physicsTheoremPromoted =
        false
    ; physicsTheoremPromotedIsFalse =
        refl
    ; gate3ClosurePromoted =
        false
    ; gate3ClosurePromotedIsFalse =
        refl
    ; clayPromotionMade =
        false
    ; clayPromotionMadeIsFalse =
        refl
    ; boundaries =
        canonicalDialecticalCarrierFrontierBoundaries
    ; boundariesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        dialecticalCarrierFrontierPromotionImpossibleHere
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    }

canonicalDialecticalCarrierFrontierNoPhysicsTheorem :
  physicsTheoremPromoted canonicalDialecticalCarrierFrontierReceipt ≡ false
canonicalDialecticalCarrierFrontierNoPhysicsTheorem =
  refl

canonicalDialecticalCarrierFrontierNoGate3Closure :
  gate3ClosurePromoted canonicalDialecticalCarrierFrontierReceipt ≡ false
canonicalDialecticalCarrierFrontierNoGate3Closure =
  refl

canonicalDialecticalCarrierFrontierNoClayPromotion :
  clayPromotionMade canonicalDialecticalCarrierFrontierReceipt ≡ false
canonicalDialecticalCarrierFrontierNoClayPromotion =
  refl
