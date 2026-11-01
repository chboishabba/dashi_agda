module DASHI.Physics.Closure.FriendshipCarryAbsorptionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DialecticalModulusLadderReceipt as Modulus
import DASHI.Reasoning.DialecticalDepthAccumulationReceipt as Depth

------------------------------------------------------------------------
-- Friendship/carry absorption receipt.
--
-- This receipt records a bounded semantic closure only:
--
-- * the other kept permanently external reintroduces live pressure;
-- * the other included in the self-model/evaluative basis converts that
--   pressure into depth/history;
-- * the friendship candidate is not agreement, but the ability to evaluate
--   from the other's basis;
-- * 6 -> 9 is recorded as pressure-to-depth absorption, not as adding more
--   threads.
--
-- It deliberately remains candidate/bookkeeping.  No social theorem, runtime
-- codec, analytical physics theorem, Clay promotion, or terminal theorem is
-- claimed.

data FriendshipCarryAbsorptionStatus : Set where
  friendshipCarryAbsorptionRecordedCandidateBookkeeping :
    FriendshipCarryAbsorptionStatus

data OtherPlacement : Set where
  otherPermanentlyExternal :
    OtherPlacement

  otherIncludedInSelfModelEvaluativeBasis :
    OtherPlacement

data PressureCarryReading : Set where
  externalOtherReintroducesLivePressure :
    PressureCarryReading

  includedOtherConvertsPressureToDepthHistoryReading :
    PressureCarryReading

data FriendshipCandidateReading : Set where
  friendshipAsOtherBasisEvaluationNotAgreement :
    FriendshipCandidateReading

data SixNineCarryAbsorption : Set where
  sixToNinePressureToDepthAbsorptionNoThreadAddition :
    SixNineCarryAbsorption

data FriendshipCarryAbsorptionNonClaim : Set where
  noFriendshipTheorem :
    FriendshipCarryAbsorptionNonClaim

  noAgreementTheorem :
    FriendshipCarryAbsorptionNonClaim

  noRuntimeCodec :
    FriendshipCarryAbsorptionNonClaim

  noSocialPsychologyTheorem :
    FriendshipCarryAbsorptionNonClaim

  noPhysicsTheorem :
    FriendshipCarryAbsorptionNonClaim

  noClayPromotion :
    FriendshipCarryAbsorptionNonClaim

  noTerminalPromotion :
    FriendshipCarryAbsorptionNonClaim

canonicalFriendshipCarryAbsorptionNonClaims :
  List FriendshipCarryAbsorptionNonClaim
canonicalFriendshipCarryAbsorptionNonClaims =
  noFriendshipTheorem
  ∷ noAgreementTheorem
  ∷ noRuntimeCodec
  ∷ noSocialPsychologyTheorem
  ∷ noPhysicsTheorem
  ∷ noClayPromotion
  ∷ noTerminalPromotion
  ∷ []

data FriendshipCarryAbsorptionPromotion : Set where

friendshipCarryAbsorptionPromotionImpossibleHere :
  FriendshipCarryAbsorptionPromotion →
  ⊥
friendshipCarryAbsorptionPromotionImpossibleHere ()

modSix :
  Nat
modSix =
  6

modNine :
  Nat
modNine =
  9

externalOtherPressureStatement :
  String
externalOtherPressureStatement =
  "Keeping the other permanently external reintroduces live pressure."

includedOtherDepthStatement :
  String
includedOtherDepthStatement =
  "Including the other in the self-model and evaluative basis converts pressure into depth/history."

friendshipCandidateStatement :
  String
friendshipCandidateStatement =
  "The friendship candidate is not agreement; it records the ability to evaluate from the other's basis."

sixNineAbsorptionStatement :
  String
sixNineAbsorptionStatement =
  "6 -> 9 is pressure-to-depth absorption, not adding more threads."

boundaryStatement :
  String
boundaryStatement =
  "Candidate/bookkeeping only: all proof, runtime, physics, Clay, and terminal promotion flags remain false."

record FriendshipCarryAbsorptionReceipt : Setω where
  field
    status :
      FriendshipCarryAbsorptionStatus

    statusIsCandidateBookkeeping :
      status ≡ friendshipCarryAbsorptionRecordedCandidateBookkeeping

    depthReceipt :
      Depth.DialecticalDepthAccumulationReceipt

    depthReceiptKeepsFriendshipTheoremFalse :
      Depth.friendshipTheoremProved depthReceipt ≡ false

    depthReceiptKeepsPressureModelUnvalidated :
      Depth.pressureModelValidated depthReceipt ≡ false

    modulusReceipt :
      Modulus.DialecticalModulusLadderReceipt

    modulusReceiptKeepsSocialTheoremFalse :
      Modulus.socialTheoremClaimed modulusReceipt ≡ false

    modulusReceiptKeepsClayPromotionFalse :
      Modulus.clayPromotionClaimed modulusReceipt ≡ false

    externalPlacement :
      OtherPlacement

    externalPlacementIsCanonical :
      externalPlacement ≡ otherPermanentlyExternal

    externalPressureReading :
      PressureCarryReading

    externalPressureReadingIsLivePressure :
      externalPressureReading ≡ externalOtherReintroducesLivePressure

    externalOtherReintroducesPressure :
      Bool

    externalOtherReintroducesPressureIsTrue :
      externalOtherReintroducesPressure ≡ true

    includedPlacement :
      OtherPlacement

    includedPlacementIsCanonical :
      includedPlacement ≡ otherIncludedInSelfModelEvaluativeBasis

    includedDepthReading :
      PressureCarryReading

    includedDepthReadingIsDepthHistory :
      includedDepthReading ≡ includedOtherConvertsPressureToDepthHistoryReading

    includedOtherConvertsPressureToDepthHistory :
      Bool

    includedOtherConvertsPressureToDepthHistoryIsTrue :
      includedOtherConvertsPressureToDepthHistory ≡ true

    friendshipCandidate :
      FriendshipCandidateReading

    friendshipCandidateIsOtherBasisEvaluation :
      friendshipCandidate ≡ friendshipAsOtherBasisEvaluationNotAgreement

    friendshipIsAgreement :
      Bool

    friendshipIsAgreementIsFalse :
      friendshipIsAgreement ≡ false

    evaluatesFromOtherBasis :
      Bool

    evaluatesFromOtherBasisIsTrue :
      evaluatesFromOtherBasis ≡ true

    sourceModulus :
      Nat

    sourceModulusIsSix :
      sourceModulus ≡ modSix

    absorbedModulus :
      Nat

    absorbedModulusIsNine :
      absorbedModulus ≡ modNine

    absorptionReading :
      SixNineCarryAbsorption

    absorptionReadingIsCanonical :
      absorptionReading ≡ sixToNinePressureToDepthAbsorptionNoThreadAddition

    sixToNineAddsThreads :
      Bool

    sixToNineAddsThreadsIsFalse :
      sixToNineAddsThreads ≡ false

    theoremStatusCandidateOnly :
      Bool

    theoremStatusCandidateOnlyIsTrue :
      theoremStatusCandidateOnly ≡ true

    friendshipTheoremProved :
      Bool

    friendshipTheoremProvedIsFalse :
      friendshipTheoremProved ≡ false

    agreementTheoremProved :
      Bool

    agreementTheoremProvedIsFalse :
      agreementTheoremProved ≡ false

    pressureAbsorptionTheoremProved :
      Bool

    pressureAbsorptionTheoremProvedIsFalse :
      pressureAbsorptionTheoremProved ≡ false

    runtimeCodecClaimed :
      Bool

    runtimeCodecClaimedIsFalse :
      runtimeCodecClaimed ≡ false

    physicsTheoremClaimed :
      Bool

    physicsTheoremClaimedIsFalse :
      physicsTheoremClaimed ≡ false

    clayPromotionClaimed :
      Bool

    clayPromotionClaimedIsFalse :
      clayPromotionClaimed ≡ false

    terminalPromotionClaimed :
      Bool

    terminalPromotionClaimedIsFalse :
      terminalPromotionClaimed ≡ false

    nonClaims :
      List FriendshipCarryAbsorptionNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalFriendshipCarryAbsorptionNonClaims

    promotionFlags :
      List FriendshipCarryAbsorptionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    externalOtherText :
      String

    externalOtherTextIsCanonical :
      externalOtherText ≡ externalOtherPressureStatement

    includedOtherText :
      String

    includedOtherTextIsCanonical :
      includedOtherText ≡ includedOtherDepthStatement

    friendshipCandidateText :
      String

    friendshipCandidateTextIsCanonical :
      friendshipCandidateText ≡ friendshipCandidateStatement

    sixNineAbsorptionText :
      String

    sixNineAbsorptionTextIsCanonical :
      sixNineAbsorptionText ≡ sixNineAbsorptionStatement

    boundaryText :
      String

    boundaryTextIsCanonical :
      boundaryText ≡ boundaryStatement

    receiptBoundary :
      List String

open FriendshipCarryAbsorptionReceipt public

canonicalFriendshipCarryAbsorptionReceipt :
  FriendshipCarryAbsorptionReceipt
canonicalFriendshipCarryAbsorptionReceipt =
  record
    { status =
        friendshipCarryAbsorptionRecordedCandidateBookkeeping
    ; statusIsCandidateBookkeeping =
        refl
    ; depthReceipt =
        Depth.canonicalDialecticalDepthAccumulationReceipt
    ; depthReceiptKeepsFriendshipTheoremFalse =
        refl
    ; depthReceiptKeepsPressureModelUnvalidated =
        refl
    ; modulusReceipt =
        Modulus.canonicalDialecticalModulusLadderReceipt
    ; modulusReceiptKeepsSocialTheoremFalse =
        refl
    ; modulusReceiptKeepsClayPromotionFalse =
        refl
    ; externalPlacement =
        otherPermanentlyExternal
    ; externalPlacementIsCanonical =
        refl
    ; externalPressureReading =
        externalOtherReintroducesLivePressure
    ; externalPressureReadingIsLivePressure =
        refl
    ; externalOtherReintroducesPressure =
        true
    ; externalOtherReintroducesPressureIsTrue =
        refl
    ; includedPlacement =
        otherIncludedInSelfModelEvaluativeBasis
    ; includedPlacementIsCanonical =
        refl
    ; includedDepthReading =
        includedOtherConvertsPressureToDepthHistoryReading
    ; includedDepthReadingIsDepthHistory =
        refl
    ; includedOtherConvertsPressureToDepthHistory =
        true
    ; includedOtherConvertsPressureToDepthHistoryIsTrue =
        refl
    ; friendshipCandidate =
        friendshipAsOtherBasisEvaluationNotAgreement
    ; friendshipCandidateIsOtherBasisEvaluation =
        refl
    ; friendshipIsAgreement =
        false
    ; friendshipIsAgreementIsFalse =
        refl
    ; evaluatesFromOtherBasis =
        true
    ; evaluatesFromOtherBasisIsTrue =
        refl
    ; sourceModulus =
        modSix
    ; sourceModulusIsSix =
        refl
    ; absorbedModulus =
        modNine
    ; absorbedModulusIsNine =
        refl
    ; absorptionReading =
        sixToNinePressureToDepthAbsorptionNoThreadAddition
    ; absorptionReadingIsCanonical =
        refl
    ; sixToNineAddsThreads =
        false
    ; sixToNineAddsThreadsIsFalse =
        refl
    ; theoremStatusCandidateOnly =
        true
    ; theoremStatusCandidateOnlyIsTrue =
        refl
    ; friendshipTheoremProved =
        false
    ; friendshipTheoremProvedIsFalse =
        refl
    ; agreementTheoremProved =
        false
    ; agreementTheoremProvedIsFalse =
        refl
    ; pressureAbsorptionTheoremProved =
        false
    ; pressureAbsorptionTheoremProvedIsFalse =
        refl
    ; runtimeCodecClaimed =
        false
    ; runtimeCodecClaimedIsFalse =
        refl
    ; physicsTheoremClaimed =
        false
    ; physicsTheoremClaimedIsFalse =
        refl
    ; clayPromotionClaimed =
        false
    ; clayPromotionClaimedIsFalse =
        refl
    ; terminalPromotionClaimed =
        false
    ; terminalPromotionClaimedIsFalse =
        refl
    ; nonClaims =
        canonicalFriendshipCarryAbsorptionNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; externalOtherText =
        externalOtherPressureStatement
    ; externalOtherTextIsCanonical =
        refl
    ; includedOtherText =
        includedOtherDepthStatement
    ; includedOtherTextIsCanonical =
        refl
    ; friendshipCandidateText =
        friendshipCandidateStatement
    ; friendshipCandidateTextIsCanonical =
        refl
    ; sixNineAbsorptionText =
        sixNineAbsorptionStatement
    ; sixNineAbsorptionTextIsCanonical =
        refl
    ; boundaryText =
        boundaryStatement
    ; boundaryTextIsCanonical =
        refl
    ; receiptBoundary =
        "Records permanent external-other mode as live pressure reintroduction"
        ∷ "Records included-other self-model basis as pressure converted to depth/history"
        ∷ "Records friendship candidate as other-basis evaluation, not agreement"
        ∷ "Records 6 -> 9 as pressure-to-depth absorption, not additional threads"
        ∷ "Imports existing depth/modulus receipts while preserving their false theorem flags"
        ∷ "No runtime codec, social theorem, physics theorem, Clay promotion, or terminal promotion follows"
        ∷ []
    }

canonicalFriendshipCarryAbsorptionNoFriendshipTheorem :
  friendshipTheoremProved canonicalFriendshipCarryAbsorptionReceipt
  ≡
  false
canonicalFriendshipCarryAbsorptionNoFriendshipTheorem =
  refl

canonicalFriendshipCarryAbsorptionNoAgreementTheorem :
  agreementTheoremProved canonicalFriendshipCarryAbsorptionReceipt
  ≡
  false
canonicalFriendshipCarryAbsorptionNoAgreementTheorem =
  refl

canonicalFriendshipCarryAbsorptionNoThreadAddition :
  sixToNineAddsThreads canonicalFriendshipCarryAbsorptionReceipt
  ≡
  false
canonicalFriendshipCarryAbsorptionNoThreadAddition =
  refl

canonicalFriendshipCarryAbsorptionNoPromotion :
  promotionFlags canonicalFriendshipCarryAbsorptionReceipt ≡ []
canonicalFriendshipCarryAbsorptionNoPromotion =
  refl
