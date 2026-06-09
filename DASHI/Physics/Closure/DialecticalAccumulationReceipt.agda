module DASHI.Physics.Closure.DialecticalAccumulationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Dialectical accumulation receipt.
--
-- This receipt records discourse/position bookkeeping only:
--
-- * base positions are balanced ternary {-1,0,+1};
-- * +1 + +1 overflows as plusTwo and must be resolved by subsumption,
--   raw overwhelm, or systematisation/supervoxel pop;
-- * the supervoxel pop is the BT/FRACTRAN carry where the current level
--   becomes subvoxel/neutral and depth increases;
-- * +1 + -1 cancels to neutral.
--
-- It does not prove a physics theorem and does not make a Clay claim.

data DialecticalAccumulationStatus : Set where
  dialecticalAccumulationBookkeepingRecordedFailClosed :
    DialecticalAccumulationStatus

data BaseTernaryPosition : Set where
  minusOnePosition :
    BaseTernaryPosition

  neutralZeroPosition :
    BaseTernaryPosition

  plusOnePosition :
    BaseTernaryPosition

canonicalBaseTernaryPositions :
  List BaseTernaryPosition
canonicalBaseTernaryPositions =
  minusOnePosition
  ∷ neutralZeroPosition
  ∷ plusOnePosition
  ∷ []

data AccumulationRule : Set where
  plusOnePlusPlusOneOverflowsToPlusTwo :
    AccumulationRule

  plusOnePlusMinusOneCancelsToNeutral :
    AccumulationRule

canonicalAccumulationRules :
  List AccumulationRule
canonicalAccumulationRules =
  plusOnePlusPlusOneOverflowsToPlusTwo
  ∷ plusOnePlusMinusOneCancelsToNeutral
  ∷ []

data OverflowOutcome : Set where
  subsumedIntoSubvoxel :
    OverflowOutcome

  overwhelmedRawPlusTwo :
    OverflowOutcome

  systematisedSupervoxelPopPlusTwenty :
    OverflowOutcome

canonicalOverflowOutcomes :
  List OverflowOutcome
canonicalOverflowOutcomes =
  subsumedIntoSubvoxel
  ∷ overwhelmedRawPlusTwo
  ∷ systematisedSupervoxelPopPlusTwenty
  ∷ []

data CarryReading : Set where
  btFractranCarryCurrentLevelNeutralDepthIncreases :
    CarryReading

data CancellationReading : Set where
  oppositionCancelsToNeutral :
    CancellationReading

data DialecticalAccumulationNonClaim : Set where
  noPhysicsTheoremClaim :
    DialecticalAccumulationNonClaim

  noClayClaim :
    DialecticalAccumulationNonClaim

canonicalDialecticalAccumulationNonClaims :
  List DialecticalAccumulationNonClaim
canonicalDialecticalAccumulationNonClaims =
  noPhysicsTheoremClaim
  ∷ noClayClaim
  ∷ []

data DialecticalAccumulationPromotion : Set where

dialecticalAccumulationPromotionImpossibleHere :
  DialecticalAccumulationPromotion →
  ⊥
dialecticalAccumulationPromotionImpossibleHere ()

baseTernarySummary :
  String
baseTernarySummary =
  "Base discourse positions are balanced ternary: -1, 0, and +1."

overflowSummary :
  String
overflowSummary =
  "+1 + +1 gives overflow/plusTwo and must resolve as subvoxel subsumption, raw +2 overwhelm, or systematised +20 supervoxel pop."

carrySummary :
  String
carrySummary =
  "Supervoxel pop is the BT/FRACTRAN carry: the current level becomes subvoxel/neutral and depth increases."

cancellationSummary :
  String
cancellationSummary =
  "+1 + -1 cancels to neutral."

boundarySummary :
  String
boundarySummary =
  "This receipt records discourse and position bookkeeping only; it proves no physics theorem and makes no Clay claim."

record DialecticalAccumulationReceipt : Setω where
  field
    status :
      DialecticalAccumulationStatus

    statusIsFailClosed :
      status ≡ dialecticalAccumulationBookkeepingRecordedFailClosed

    basePositions :
      List BaseTernaryPosition

    basePositionsAreCanonical :
      basePositions ≡ canonicalBaseTernaryPositions

    basePositionCount :
      Nat

    basePositionCountIsThree :
      basePositionCount ≡ 3

    minusOneGlyph :
      String

    minusOneGlyphIsCanonical :
      minusOneGlyph ≡ "-1"

    neutralGlyph :
      String

    neutralGlyphIsCanonical :
      neutralGlyph ≡ "0"

    plusOneGlyph :
      String

    plusOneGlyphIsCanonical :
      plusOneGlyph ≡ "+1"

    accumulationRules :
      List AccumulationRule

    accumulationRulesAreCanonical :
      accumulationRules ≡ canonicalAccumulationRules

    plusOneAddendLeft :
      BaseTernaryPosition

    plusOneAddendLeftIsCanonical :
      plusOneAddendLeft ≡ plusOnePosition

    plusOneAddendRight :
      BaseTernaryPosition

    plusOneAddendRightIsCanonical :
      plusOneAddendRight ≡ plusOnePosition

    overflowValue :
      Nat

    overflowValueIsPlusTwo :
      overflowValue ≡ 2

    overflowNotation :
      String

    overflowNotationIsCanonical :
      overflowNotation ≡ "+2"

    overflowOutcomes :
      List OverflowOutcome

    overflowOutcomesAreCanonical :
      overflowOutcomes ≡ canonicalOverflowOutcomes

    overflowOutcomeCount :
      Nat

    overflowOutcomeCountIsThree :
      overflowOutcomeCount ≡ 3

    subvoxelOutcome :
      OverflowOutcome

    subvoxelOutcomeIsCanonical :
      subvoxelOutcome ≡ subsumedIntoSubvoxel

    rawPlusTwoOutcome :
      OverflowOutcome

    rawPlusTwoOutcomeIsCanonical :
      rawPlusTwoOutcome ≡ overwhelmedRawPlusTwo

    supervoxelOutcome :
      OverflowOutcome

    supervoxelOutcomeIsCanonical :
      supervoxelOutcome ≡ systematisedSupervoxelPopPlusTwenty

    supervoxelPopNotation :
      String

    supervoxelPopNotationIsCanonical :
      supervoxelPopNotation ≡ "+20"

    carryReading :
      CarryReading

    carryReadingIsCanonical :
      carryReading ≡ btFractranCarryCurrentLevelNeutralDepthIncreases

    currentLevelAfterCarry :
      BaseTernaryPosition

    currentLevelAfterCarryIsNeutral :
      currentLevelAfterCarry ≡ neutralZeroPosition

    depthIncrease :
      Nat

    depthIncreaseIsOne :
      depthIncrease ≡ 1

    cancellationLeft :
      BaseTernaryPosition

    cancellationLeftIsPlusOne :
      cancellationLeft ≡ plusOnePosition

    cancellationRight :
      BaseTernaryPosition

    cancellationRightIsMinusOne :
      cancellationRight ≡ minusOnePosition

    cancellationResult :
      BaseTernaryPosition

    cancellationResultIsNeutral :
      cancellationResult ≡ neutralZeroPosition

    cancellationReading :
      CancellationReading

    cancellationReadingIsCanonical :
      cancellationReading ≡ oppositionCancelsToNeutral

    discoursePositionBookkeepingOnly :
      Bool

    discoursePositionBookkeepingOnlyIsTrue :
      discoursePositionBookkeepingOnly ≡ true

    physicsTheoremClaimed :
      Bool

    physicsTheoremClaimedIsFalse :
      physicsTheoremClaimed ≡ false

    clayClaimMade :
      Bool

    clayClaimMadeIsFalse :
      clayClaimMade ≡ false

    promotionFlags :
      List DialecticalAccumulationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    nonClaims :
      List DialecticalAccumulationNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalDialecticalAccumulationNonClaims

    noPromotion :
      DialecticalAccumulationPromotion →
      ⊥

    baseTernaryReading :
      String

    baseTernaryReadingIsCanonical :
      baseTernaryReading ≡ baseTernarySummary

    overflowReading :
      String

    overflowReadingIsCanonical :
      overflowReading ≡ overflowSummary

    carryReadingSummary :
      String

    carryReadingSummaryIsCanonical :
      carryReadingSummary ≡ carrySummary

    cancellationReadingSummary :
      String

    cancellationReadingSummaryIsCanonical :
      cancellationReadingSummary ≡ cancellationSummary

    boundaryReading :
      String

    boundaryReadingIsCanonical :
      boundaryReading ≡ boundarySummary

    receiptBoundary :
      List String

open DialecticalAccumulationReceipt public

canonicalDialecticalAccumulationReceipt :
  DialecticalAccumulationReceipt
canonicalDialecticalAccumulationReceipt =
  record
    { status =
        dialecticalAccumulationBookkeepingRecordedFailClosed
    ; statusIsFailClosed =
        refl
    ; basePositions =
        canonicalBaseTernaryPositions
    ; basePositionsAreCanonical =
        refl
    ; basePositionCount =
        3
    ; basePositionCountIsThree =
        refl
    ; minusOneGlyph =
        "-1"
    ; minusOneGlyphIsCanonical =
        refl
    ; neutralGlyph =
        "0"
    ; neutralGlyphIsCanonical =
        refl
    ; plusOneGlyph =
        "+1"
    ; plusOneGlyphIsCanonical =
        refl
    ; accumulationRules =
        canonicalAccumulationRules
    ; accumulationRulesAreCanonical =
        refl
    ; plusOneAddendLeft =
        plusOnePosition
    ; plusOneAddendLeftIsCanonical =
        refl
    ; plusOneAddendRight =
        plusOnePosition
    ; plusOneAddendRightIsCanonical =
        refl
    ; overflowValue =
        2
    ; overflowValueIsPlusTwo =
        refl
    ; overflowNotation =
        "+2"
    ; overflowNotationIsCanonical =
        refl
    ; overflowOutcomes =
        canonicalOverflowOutcomes
    ; overflowOutcomesAreCanonical =
        refl
    ; overflowOutcomeCount =
        3
    ; overflowOutcomeCountIsThree =
        refl
    ; subvoxelOutcome =
        subsumedIntoSubvoxel
    ; subvoxelOutcomeIsCanonical =
        refl
    ; rawPlusTwoOutcome =
        overwhelmedRawPlusTwo
    ; rawPlusTwoOutcomeIsCanonical =
        refl
    ; supervoxelOutcome =
        systematisedSupervoxelPopPlusTwenty
    ; supervoxelOutcomeIsCanonical =
        refl
    ; supervoxelPopNotation =
        "+20"
    ; supervoxelPopNotationIsCanonical =
        refl
    ; carryReading =
        btFractranCarryCurrentLevelNeutralDepthIncreases
    ; carryReadingIsCanonical =
        refl
    ; currentLevelAfterCarry =
        neutralZeroPosition
    ; currentLevelAfterCarryIsNeutral =
        refl
    ; depthIncrease =
        1
    ; depthIncreaseIsOne =
        refl
    ; cancellationLeft =
        plusOnePosition
    ; cancellationLeftIsPlusOne =
        refl
    ; cancellationRight =
        minusOnePosition
    ; cancellationRightIsMinusOne =
        refl
    ; cancellationResult =
        neutralZeroPosition
    ; cancellationResultIsNeutral =
        refl
    ; cancellationReading =
        oppositionCancelsToNeutral
    ; cancellationReadingIsCanonical =
        refl
    ; discoursePositionBookkeepingOnly =
        true
    ; discoursePositionBookkeepingOnlyIsTrue =
        refl
    ; physicsTheoremClaimed =
        false
    ; physicsTheoremClaimedIsFalse =
        refl
    ; clayClaimMade =
        false
    ; clayClaimMadeIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; nonClaims =
        canonicalDialecticalAccumulationNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; noPromotion =
        dialecticalAccumulationPromotionImpossibleHere
    ; baseTernaryReading =
        baseTernarySummary
    ; baseTernaryReadingIsCanonical =
        refl
    ; overflowReading =
        overflowSummary
    ; overflowReadingIsCanonical =
        refl
    ; carryReadingSummary =
        carrySummary
    ; carryReadingSummaryIsCanonical =
        refl
    ; cancellationReadingSummary =
        cancellationSummary
    ; cancellationReadingSummaryIsCanonical =
        refl
    ; boundaryReading =
        boundarySummary
    ; boundaryReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Base ternary positions are -1, 0, and +1"
        ∷ "+1 + +1 is recorded as overflow/plusTwo"
        ∷ "Overflow resolves as subvoxel subsumption, raw +2 overwhelm, or +20 supervoxel pop"
        ∷ "Supervoxel pop is the BT/FRACTRAN carry: current level neutral, depth increases by one"
        ∷ "+1 + -1 cancels to neutral"
        ∷ "This is discourse/position bookkeeping only: no physics theorem and no Clay claim"
        ∷ []
    }

canonicalDialecticalAccumulationKeepsPhysicsTheoremFalse :
  physicsTheoremClaimed canonicalDialecticalAccumulationReceipt ≡ false
canonicalDialecticalAccumulationKeepsPhysicsTheoremFalse =
  refl

canonicalDialecticalAccumulationKeepsClayFalse :
  clayClaimMade canonicalDialecticalAccumulationReceipt ≡ false
canonicalDialecticalAccumulationKeepsClayFalse =
  refl

canonicalDialecticalAccumulationNoPromotion :
  DialecticalAccumulationPromotion →
  ⊥
canonicalDialecticalAccumulationNoPromotion =
  dialecticalAccumulationPromotionImpossibleHere
