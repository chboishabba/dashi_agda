module DASHI.Physics.Closure.CarrierCarryProjectionDefectReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Carrier carry / projection-defect receipt.
--
-- This module records the bookkeeping reading:
--
--   +1_k + +1_k = (-1_k , +1_(k+1)).
--
-- P_s(x) is the promoted synthesis at depth k+1, read here as the
-- supervoxel pop / what the carrier became.  D_s(x) is the residual defect
-- at depth k, read here as memory / what must not be forgotten.
--
-- Dropping the carry is the mod-3 trap.  Keeping the carry is dialectical
-- elevation.  Any residual r in carrier state is tracked fail-closed as an
-- unabsorbed or dropped carry.  Re-encounter / mod-6 memory is diagnostic
-- text only.  No arithmetic theorem, runtime codec proof, physics theorem,
-- or Clay promotion is claimed here.

data CarrierCarryStatus : Set where
  projectionDefectBookkeepingRecorded :
    CarrierCarryStatus

data CarrierCarryRule : Set where
  plusOnePlusPlusOneSplitsResidualAndCarry :
    CarrierCarryRule

data PromotedSynthesis : Set where
  positiveCarryAtNextDepth :
    PromotedSynthesis

data ResidualDefect : Set where
  negativeResidualAtCurrentDepth :
    ResidualDefect

data CarryRetentionReading : Set where
  droppedCarryIsMod3Trap :
    CarryRetentionReading

  keptCarryIsDialecticalElevation :
    CarryRetentionReading

data CarrierResidualState : Set where
  rTracksDroppedOrUnabsorbedCarryFailClosed :
    CarrierResidualState

data DiagnosticMemoryStatus : Set where
  reEncounterMod6MemoryDiagnosticOnly :
    DiagnosticMemoryStatus

data CarrierCarryNonClaim : Set where
  noArithmeticTheorem :
    CarrierCarryNonClaim

  noRuntimeCodecProof :
    CarrierCarryNonClaim

  noPhysicsPromotion :
    CarrierCarryNonClaim

  noClayPromotion :
    CarrierCarryNonClaim

canonicalCarrierCarryNonClaims :
  List CarrierCarryNonClaim
canonicalCarrierCarryNonClaims =
  noArithmeticTheorem
  ∷ noRuntimeCodecProof
  ∷ noPhysicsPromotion
  ∷ noClayPromotion
  ∷ []

data CarrierCarryPromotion : Set where

carrierCarryPromotionImpossibleHere :
  CarrierCarryPromotion →
  ⊥
carrierCarryPromotionImpossibleHere ()

carryRuleStatement :
  String
carryRuleStatement =
  "+1_k + +1_k = (-1_k, +1_(k+1)) as projection-defect bookkeeping."

promotedSynthesisStatement :
  String
promotedSynthesisStatement =
  "P_s(x) = +1_(k+1): promoted synthesis, supervoxel pop, what the carrier became."

residualDefectStatement :
  String
residualDefectStatement =
  "D_s(x) = -1_k: residual defect, memory, do not forget."

carryRetentionStatement :
  String
carryRetentionStatement =
  "Dropping the carry is the mod-3 trap; keeping the carry is dialectical elevation."

residualCarrierStateStatement :
  String
residualCarrierStateStatement =
  "Residual r in carrier state is a dropped or unabsorbed carry tracked fail-closed."

diagnosticMemoryStatement :
  String
diagnosticMemoryStatement =
  "Re-encounter / mod-6 memory is recorded as a diagnostic string only."

record CarrierCarryProjectionDefectReceipt : Setω where
  field
    status :
      CarrierCarryStatus

    statusIsCanonical :
      status ≡ projectionDefectBookkeepingRecorded

    carryRule :
      CarrierCarryRule

    carryRuleIsProjectionDefect :
      carryRule ≡ plusOnePlusPlusOneSplitsResidualAndCarry

    promotedSynthesis :
      PromotedSynthesis

    promotedSynthesisIsNextDepthPositive :
      promotedSynthesis ≡ positiveCarryAtNextDepth

    residualDefect :
      ResidualDefect

    residualDefectIsCurrentDepthNegative :
      residualDefect ≡ negativeResidualAtCurrentDepth

    dropCarryReading :
      CarryRetentionReading

    dropCarryReadingIsMod3Trap :
      dropCarryReading ≡ droppedCarryIsMod3Trap

    keepCarryReading :
      CarryRetentionReading

    keepCarryReadingIsDialecticalElevation :
      keepCarryReading ≡ keptCarryIsDialecticalElevation

    carrierResidualState :
      CarrierResidualState

    carrierResidualStateIsFailClosed :
      carrierResidualState ≡ rTracksDroppedOrUnabsorbedCarryFailClosed

    diagnosticMemory :
      DiagnosticMemoryStatus

    diagnosticMemoryIsStringOnly :
      diagnosticMemory ≡ reEncounterMod6MemoryDiagnosticOnly

    carryRetained :
      Bool

    carryRetainedIsTrue :
      carryRetained ≡ true

    droppedCarryAccepted :
      Bool

    droppedCarryAcceptedIsFalse :
      droppedCarryAccepted ≡ false

    arithmeticTheoremClaimed :
      Bool

    arithmeticTheoremClaimedIsFalse :
      arithmeticTheoremClaimed ≡ false

    runtimeCodecProofClaimed :
      Bool

    runtimeCodecProofClaimedIsFalse :
      runtimeCodecProofClaimed ≡ false

    physicsPromotionClaimed :
      Bool

    physicsPromotionClaimedIsFalse :
      physicsPromotionClaimed ≡ false

    clayPromotionClaimed :
      Bool

    clayPromotionClaimedIsFalse :
      clayPromotionClaimed ≡ false

    nonClaims :
      List CarrierCarryNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalCarrierCarryNonClaims

    promotionFlags :
      List CarrierCarryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    carryRuleReading :
      String

    carryRuleReadingIsCanonical :
      carryRuleReading ≡ carryRuleStatement

    promotedSynthesisReading :
      String

    promotedSynthesisReadingIsCanonical :
      promotedSynthesisReading ≡ promotedSynthesisStatement

    residualDefectReading :
      String

    residualDefectReadingIsCanonical :
      residualDefectReading ≡ residualDefectStatement

    carryRetentionReading :
      String

    carryRetentionReadingIsCanonical :
      carryRetentionReading ≡ carryRetentionStatement

    residualCarrierStateReading :
      String

    residualCarrierStateReadingIsCanonical :
      residualCarrierStateReading ≡ residualCarrierStateStatement

    diagnosticMemoryReading :
      String

    diagnosticMemoryReadingIsCanonical :
      diagnosticMemoryReading ≡ diagnosticMemoryStatement

    receiptBoundary :
      List String

open CarrierCarryProjectionDefectReceipt public

canonicalCarrierCarryProjectionDefectReceipt :
  CarrierCarryProjectionDefectReceipt
canonicalCarrierCarryProjectionDefectReceipt =
  record
    { status =
        projectionDefectBookkeepingRecorded
    ; statusIsCanonical =
        refl
    ; carryRule =
        plusOnePlusPlusOneSplitsResidualAndCarry
    ; carryRuleIsProjectionDefect =
        refl
    ; promotedSynthesis =
        positiveCarryAtNextDepth
    ; promotedSynthesisIsNextDepthPositive =
        refl
    ; residualDefect =
        negativeResidualAtCurrentDepth
    ; residualDefectIsCurrentDepthNegative =
        refl
    ; dropCarryReading =
        droppedCarryIsMod3Trap
    ; dropCarryReadingIsMod3Trap =
        refl
    ; keepCarryReading =
        keptCarryIsDialecticalElevation
    ; keepCarryReadingIsDialecticalElevation =
        refl
    ; carrierResidualState =
        rTracksDroppedOrUnabsorbedCarryFailClosed
    ; carrierResidualStateIsFailClosed =
        refl
    ; diagnosticMemory =
        reEncounterMod6MemoryDiagnosticOnly
    ; diagnosticMemoryIsStringOnly =
        refl
    ; carryRetained =
        true
    ; carryRetainedIsTrue =
        refl
    ; droppedCarryAccepted =
        false
    ; droppedCarryAcceptedIsFalse =
        refl
    ; arithmeticTheoremClaimed =
        false
    ; arithmeticTheoremClaimedIsFalse =
        refl
    ; runtimeCodecProofClaimed =
        false
    ; runtimeCodecProofClaimedIsFalse =
        refl
    ; physicsPromotionClaimed =
        false
    ; physicsPromotionClaimedIsFalse =
        refl
    ; clayPromotionClaimed =
        false
    ; clayPromotionClaimedIsFalse =
        refl
    ; nonClaims =
        canonicalCarrierCarryNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; carryRuleReading =
        carryRuleStatement
    ; carryRuleReadingIsCanonical =
        refl
    ; promotedSynthesisReading =
        promotedSynthesisStatement
    ; promotedSynthesisReadingIsCanonical =
        refl
    ; residualDefectReading =
        residualDefectStatement
    ; residualDefectReadingIsCanonical =
        refl
    ; carryRetentionReading =
        carryRetentionStatement
    ; carryRetentionReadingIsCanonical =
        refl
    ; residualCarrierStateReading =
        residualCarrierStateStatement
    ; residualCarrierStateReadingIsCanonical =
        refl
    ; diagnosticMemoryReading =
        diagnosticMemoryStatement
    ; diagnosticMemoryReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Records +1_k + +1_k as a projection-defect split into -1_k and +1_(k+1)"
        ∷ "Records P_s(x) as the promoted +1_(k+1) synthesis / supervoxel pop"
        ∷ "Records D_s(x) as the -1_k residual defect / memory"
        ∷ "Rejects dropping carry as the mod-3 trap and keeps carry as dialectical elevation"
        ∷ "Tracks residual r fail-closed as dropped or unabsorbed carry"
        ∷ "Records re-encounter / mod-6 memory as diagnostic text only"
        ∷ "No arithmetic theorem, runtime codec proof, physics promotion, or Clay promotion is claimed"
        ∷ []
    }

canonicalCarrierCarryKeepsCarry :
  carryRetained canonicalCarrierCarryProjectionDefectReceipt ≡ true
canonicalCarrierCarryKeepsCarry =
  refl

canonicalCarrierCarryDropsNoCarry :
  droppedCarryAccepted canonicalCarrierCarryProjectionDefectReceipt ≡ false
canonicalCarrierCarryDropsNoCarry =
  refl

canonicalCarrierCarryNoClayPromotion :
  clayPromotionClaimed canonicalCarrierCarryProjectionDefectReceipt ≡ false
canonicalCarrierCarryNoClayPromotion =
  refl
