module DASHI.Physics.Closure.DialecticalCarrierFrontierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ActiveLanePressureEnergyReceipt as PressureEnergy
import DASHI.Physics.Closure.CarrierCarryProjectionDefectReceipt as CarryDefect
import DASHI.Physics.Closure.CarrierStateVariableMappingReceipt as StateMap
import DASHI.Physics.Closure.DialecticalCarrierSevenSevenOneReceipt as Sharp771
import DASHI.Physics.Closure.DialecticalModulusLadderReceipt as Modulus
import DASHI.Physics.Closure.NSTailDominanceCarryAnalogyReceipt as NSTailCarry
import DASHI.Physics.Closure.SSPSevenSevenOneAtomFieldReceipt as SSP771

------------------------------------------------------------------------
-- Dialectical carrier frontier receipt.
--
-- This receipt integrates the carrier-frontier batch surfaces.  It is a
-- receipt frontier only: no physics theorem, no Gate 3 closure, and no Clay
-- promotion are introduced here.

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

  boundCarryProjectionDefectReceipt :
    BatchReceiptBinding

  boundCarrierStateVariableMappingReceipt :
    BatchReceiptBinding

  boundActiveLanePressureEnergyReceipt :
    BatchReceiptBinding

  boundModulusLadderReceipt :
    BatchReceiptBinding

  boundNSTailCarryAnalogyReceipt :
    BatchReceiptBinding

canonicalBatchReceiptBindings :
  List BatchReceiptBinding
canonicalBatchReceiptBindings =
  boundSevenSevenOneReceipt
  ∷ boundCarryProjectionDefectReceipt
  ∷ boundCarrierStateVariableMappingReceipt
  ∷ boundActiveLanePressureEnergyReceipt
  ∷ boundModulusLadderReceipt
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
  "The dialectical carrier frontier integrates the bound carrier batch receipts."

sevenSevenOneStatement :
  String
sevenSevenOneStatement =
  "Seven-seven-one is bound through the existing 15SSP 7+7+1 atom-field receipt."

boundSiblingsStatement :
  String
boundSiblingsStatement =
  "Carry projection-defect, carrier state variable mapping, active-lane pressure energy, and modulus ladder receipts are imported and checked directly."

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

    sharpenedSevenSevenOneReceipt :
      Sharp771.DialecticalCarrierSevenSevenOneReceipt

    sharpenedSevenSevenOneTotalIsFifteen :
      Sharp771.totalLaneCount sharpenedSevenSevenOneReceipt ≡ 15

    sharpenedSevenSevenOneObserverPrimeIsP71 :
      Sharp771.observerPrime sharpenedSevenSevenOneReceipt ≡ 71

    sharpenedSevenSevenOneSignNotGeom :
      Sharp771.signIsGeometricVariable sharpenedSevenSevenOneReceipt
      ≡
      false

    sharpenedSevenSevenOneNoClay :
      Sharp771.clayPromoted sharpenedSevenSevenOneReceipt ≡ false

    carryProjectionDefectReceipt :
      CarryDefect.CarrierCarryProjectionDefectReceipt

    carryProjectionDefectCarryRetained :
      CarryDefect.carryRetained carryProjectionDefectReceipt ≡ true

    carryProjectionDefectDroppedCarryRejected :
      CarryDefect.droppedCarryAccepted carryProjectionDefectReceipt
      ≡
      false

    carryProjectionDefectNoClay :
      CarryDefect.clayPromotionClaimed carryProjectionDefectReceipt
      ≡
      false

    carrierStateVariableMappingReceipt :
      StateMap.CarrierStateVariableMappingReceipt

    carrierStateVariableNoPaperOnePromotion :
      StateMap.CarrierStateVariableMappingReceipt.paperOneTheoremPromoted
        carrierStateVariableMappingReceipt
      ≡
      false

    carrierStateVariableGate3Open :
      StateMap.CarrierStateVariableMappingReceipt.gate3Closed
        carrierStateVariableMappingReceipt
      ≡
      false

    carrierStateVariableNoClay :
      StateMap.CarrierStateVariableMappingReceipt.clayPromoted
        carrierStateVariableMappingReceipt
      ≡
      false

    activeLanePressureEnergyReceipt :
      PressureEnergy.ActiveLanePressureEnergyReceipt

    activeLanePressureCanonicalTotal :
      PressureEnergy.canonicalTotal activeLanePressureEnergyReceipt ≡ 10

    activeLanePressureAnisotropyNine :
      PressureEnergy.anisotropy activeLanePressureEnergyReceipt ≡ 9

    activeLanePressureNoGate3 :
      PressureEnergy.navierStokesGate3Proved
        activeLanePressureEnergyReceipt
      ≡
      false

    activeLanePressureNoClay :
      PressureEnergy.clayPromotionPromoted
        activeLanePressureEnergyReceipt
      ≡
      false

    modulusLadderReceipt :
      Modulus.DialecticalModulusLadderReceipt

    modulusLadderFriendshipIsNine :
      Modulus.friendshipModulus modulusLadderReceipt ≡ 9

    modulusLadderCurrentKStarIsNine :
      Modulus.currentKStar modulusLadderReceipt ≡ 9

    modulusLadderNoOrdinal :
      Modulus.ordinalTheoremClaimed modulusLadderReceipt ≡ false

    modulusLadderNoClay :
      Modulus.clayPromotionClaimed modulusLadderReceipt ≡ false

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

    boundReceiptCountIsSix :
      boundReceiptCount ≡ 6

    frontierSummary :
      String

    frontierSummaryIsCanonical :
      frontierSummary ≡ frontierStatement

    sevenSevenOneSummary :
      String

    sevenSevenOneSummaryIsCanonical :
      sevenSevenOneSummary ≡ sevenSevenOneStatement

    boundSiblingsSummary :
      String

    boundSiblingsSummaryIsCanonical :
      boundSiblingsSummary ≡ boundSiblingsStatement

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
    ; sharpenedSevenSevenOneReceipt =
        Sharp771.canonicalDialecticalCarrierSevenSevenOneReceipt
    ; sharpenedSevenSevenOneTotalIsFifteen =
        refl
    ; sharpenedSevenSevenOneObserverPrimeIsP71 =
        refl
    ; sharpenedSevenSevenOneSignNotGeom =
        refl
    ; sharpenedSevenSevenOneNoClay =
        refl
    ; carryProjectionDefectReceipt =
        CarryDefect.canonicalCarrierCarryProjectionDefectReceipt
    ; carryProjectionDefectCarryRetained =
        refl
    ; carryProjectionDefectDroppedCarryRejected =
        refl
    ; carryProjectionDefectNoClay =
        refl
    ; carrierStateVariableMappingReceipt =
        StateMap.canonicalCarrierStateVariableMappingReceipt
    ; carrierStateVariableNoPaperOnePromotion =
        refl
    ; carrierStateVariableGate3Open =
        refl
    ; carrierStateVariableNoClay =
        refl
    ; activeLanePressureEnergyReceipt =
        PressureEnergy.canonicalActiveLanePressureEnergyReceipt
    ; activeLanePressureCanonicalTotal =
        refl
    ; activeLanePressureAnisotropyNine =
        refl
    ; activeLanePressureNoGate3 =
        refl
    ; activeLanePressureNoClay =
        refl
    ; modulusLadderReceipt =
        Modulus.canonicalDialecticalModulusLadderReceipt
    ; modulusLadderFriendshipIsNine =
        refl
    ; modulusLadderCurrentKStarIsNine =
        refl
    ; modulusLadderNoOrdinal =
        refl
    ; modulusLadderNoClay =
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
        6
    ; boundReceiptCountIsSix =
        refl
    ; frontierSummary =
        frontierStatement
    ; frontierSummaryIsCanonical =
        refl
    ; sevenSevenOneSummary =
        sevenSevenOneStatement
    ; sevenSevenOneSummaryIsCanonical =
        refl
    ; boundSiblingsSummary =
        boundSiblingsStatement
    ; boundSiblingsSummaryIsCanonical =
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
