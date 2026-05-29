module DASHI.Physics.QFT.FermionicLoopCSShiftReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_∸_)

import DASHI.Physics.QFT.KacMoodyLevelReceipt as Level
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as Ledger
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional

------------------------------------------------------------------------
-- Fermionic-loop Chern-Simons level-shift receipt.
--
-- This is a candidate/conditional bookkeeping receipt.  It records the
-- standard normalization T_SU2(fundamental) = 1/2 using a doubled Dynkin-index
-- integer, then records the selected sign convention in which two massive
-- Dirac fundamentals, equivalently four Weyl fundamentals, lower k=3 to
-- k_eff=1.
--
-- The receipt consumes existing finite SU(2)_L and exact-SM blocker surfaces,
-- but does not promote an exact SU(2) weak derivation, Standard Model
-- reconstruction, or G_DHR ~= G_SM identification.

data FermionLoopChainStage : Set where
  p3CSLevelCandidate :
    FermionLoopChainStage

  su2FundamentalIndexStage :
    FermionLoopChainStage

  twoDiracFourWeylShiftCandidate :
    FermionLoopChainStage

  effectiveLevelOneCandidate :
    FermionLoopChainStage

  promotionBoundaryRetained :
    FermionLoopChainStage

canonicalFermionLoopChain :
  List FermionLoopChainStage
canonicalFermionLoopChain =
  p3CSLevelCandidate
  ∷ su2FundamentalIndexStage
  ∷ twoDiracFourWeylShiftCandidate
  ∷ effectiveLevelOneCandidate
  ∷ promotionBoundaryRetained
  ∷ []

data FermionLoopCondition : Set where
  conditionalOnMassiveFermionSignConvention :
    FermionLoopCondition

  conditionalOnSU2FundamentalMatterContent :
    FermionLoopCondition

  conditionalOnNoExactWeakPromotion :
    FermionLoopCondition

canonicalFermionLoopConditions :
  List FermionLoopCondition
canonicalFermionLoopConditions =
  conditionalOnMassiveFermionSignConvention
  ∷ conditionalOnSU2FundamentalMatterContent
  ∷ conditionalOnNoExactWeakPromotion
  ∷ []

data FermionLoopResidualBlocker : Set where
  missingExactSU2WeakDerivation :
    FermionLoopResidualBlocker

  missingExactSMReconstruction :
    FermionLoopResidualBlocker

  missingExactGDHREqualsGSMIdentification :
    FermionLoopResidualBlocker

canonicalFermionLoopResidualBlockers :
  List FermionLoopResidualBlocker
canonicalFermionLoopResidualBlockers =
  missingExactSU2WeakDerivation
  ∷ missingExactSMReconstruction
  ∷ missingExactGDHREqualsGSMIdentification
  ∷ []

su2FundamentalDynkinIndexLabel :
  String
su2FundamentalDynkinIndexLabel =
  "SU(2) fundamental Dynkin index is T(fund)=1/2; doubled index is 1"

fermionShiftConventionLabel :
  String
fermionShiftConventionLabel =
  "candidate convention: integrating out two massive Dirac SU(2) fundamentals, equivalently four Weyl fundamentals, shifts k by -2"

effectiveLevelLabel :
  String
effectiveLevelLabel =
  "candidate level chain records k=3 -> k_eff=1 after the fermionic loop shift"

promotionBoundaryLabel :
  String
promotionBoundaryLabel =
  "exact SU(2) weak derivation, SM reconstruction, and G_DHR ~= G_SM promotion remain false"

canonicalFermionLoopBoundary :
  List String
canonicalFermionLoopBoundary =
  su2FundamentalDynkinIndexLabel
  ∷ fermionShiftConventionLabel
  ∷ effectiveLevelLabel
  ∷ promotionBoundaryLabel
  ∷ []

csEffectiveLevel :
  Nat →
  Nat →
  Nat
csEffectiveLevel bareLevel fermionShift =
  bareLevel ∸ fermionShift

su2FundamentalDoubledDynkinIndex :
  Nat
su2FundamentalDoubledDynkinIndex =
  1

diracFundamentalShiftContribution :
  Nat
diracFundamentalShiftContribution =
  su2FundamentalDoubledDynkinIndex

twoDiracFundamentalShiftContribution :
  Nat
twoDiracFundamentalShiftContribution =
  2 * diracFundamentalShiftContribution

weylFundamentalPairs :
  Nat
weylFundamentalPairs =
  4

fourWeylAsTwoDiracShiftContribution :
  Nat
fourWeylAsTwoDiracShiftContribution =
  twoDiracFundamentalShiftContribution

p3BareChernSimonsLevel :
  Nat
p3BareChernSimonsLevel =
  3

p3FermionShift :
  Nat
p3FermionShift =
  twoDiracFundamentalShiftContribution

p3EffectiveChernSimonsLevel :
  Nat
p3EffectiveChernSimonsLevel =
  csEffectiveLevel p3BareChernSimonsLevel p3FermionShift

record FermionicLoopLevelShiftComputation : Set where
  field
    bareLevel :
      Nat

    bareLevelIsThree :
      bareLevel ≡ 3

    doubledDynkinIndex :
      Nat

    doubledDynkinIndexIsOne :
      doubledDynkinIndex ≡ su2FundamentalDoubledDynkinIndex

    diracCount :
      Nat

    diracCountIsTwo :
      diracCount ≡ 2

    weylCount :
      Nat

    weylCountIsFour :
      weylCount ≡ 4

    diracShiftContribution :
      Nat

    diracShiftContributionIsTwo :
      diracShiftContribution ≡ 2

    fourWeylShiftContribution :
      Nat

    fourWeylShiftContributionMatchesTwoDirac :
      fourWeylShiftContribution ≡ diracShiftContribution

    effectiveLevel :
      Nat

    effectiveLevelIsBareMinusShift :
      effectiveLevel ≡ csEffectiveLevel bareLevel diracShiftContribution

    effectiveLevelIsOne :
      effectiveLevel ≡ 1

open FermionicLoopLevelShiftComputation public

canonicalFermionicLoopLevelShiftComputation :
  FermionicLoopLevelShiftComputation
canonicalFermionicLoopLevelShiftComputation =
  record
    { bareLevel =
        p3BareChernSimonsLevel
    ; bareLevelIsThree =
        refl
    ; doubledDynkinIndex =
        su2FundamentalDoubledDynkinIndex
    ; doubledDynkinIndexIsOne =
        refl
    ; diracCount =
        2
    ; diracCountIsTwo =
        refl
    ; weylCount =
        weylFundamentalPairs
    ; weylCountIsFour =
        refl
    ; diracShiftContribution =
        p3FermionShift
    ; diracShiftContributionIsTwo =
        refl
    ; fourWeylShiftContribution =
        fourWeylAsTwoDiracShiftContribution
    ; fourWeylShiftContributionMatchesTwoDirac =
        refl
    ; effectiveLevel =
        p3EffectiveChernSimonsLevel
    ; effectiveLevelIsBareMinusShift =
        refl
    ; effectiveLevelIsOne =
        refl
    }

record FermionicLoopCSShiftReceipt : Setω where
  field
    levelReceipt :
      Level.KacMoodyLevelReceipt

    p3ChernSimonsCandidate :
      Level.LevelReading

    p3ChernSimonsCandidateIsCanonical :
      p3ChernSimonsCandidate
      ≡
      Level.p3Conductor3ChernSimonsLevel3Candidate

    finiteSU2LRow :
      Ledger.FinitePrimeLaneSMRow

    finiteSU2LRowIsCanonical :
      finiteSU2LRow ≡ Ledger.p3SU2LFinitePrimeLaneSMRow

    exactSMBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    conditionalGDHRSMPromotionReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    conditionalGDHRStatusStillFalse :
      Conditional.unconditionalGDHREqualsGSMPromoted
        conditionalGDHRSMPromotionReceipt
      ≡
      false

    chain :
      List FermionLoopChainStage

    chainIsCanonical :
      chain ≡ canonicalFermionLoopChain

    conditions :
      List FermionLoopCondition

    conditionsAreCanonical :
      conditions ≡ canonicalFermionLoopConditions

    shiftComputation :
      FermionicLoopLevelShiftComputation

    shiftComputationIsCanonical :
      shiftComputation ≡ canonicalFermionicLoopLevelShiftComputation

    su2FundamentalIndexRecorded :
      Bool

    su2FundamentalIndexRecordedIsTrue :
      su2FundamentalIndexRecorded ≡ true

    twoDiracContributionRecorded :
      Bool

    twoDiracContributionRecordedIsTrue :
      twoDiracContributionRecorded ≡ true

    fourWeylContributionRecorded :
      Bool

    fourWeylContributionRecordedIsTrue :
      fourWeylContributionRecorded ≡ true

    kThreeToKEffOneCandidate :
      Bool

    kThreeToKEffOneCandidateIsTrue :
      kThreeToKEffOneCandidate ≡ true

    exactSU2WeakDerivation :
      Bool

    exactSU2WeakDerivationIsFalse :
      exactSU2WeakDerivation ≡ false

    exactSMReconstruction :
      Bool

    exactSMReconstructionIsFalse :
      exactSMReconstruction ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    residualBlockers :
      List FermionLoopResidualBlocker

    residualBlockersAreCanonical :
      residualBlockers ≡ canonicalFermionLoopResidualBlockers

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalFermionLoopBoundary

open FermionicLoopCSShiftReceipt public

canonicalFermionicLoopCSShiftReceipt :
  FermionicLoopCSShiftReceipt
canonicalFermionicLoopCSShiftReceipt =
  record
    { levelReceipt =
        Level.canonicalKacMoodyLevelReceipt
    ; p3ChernSimonsCandidate =
        Level.p3ChernSimonsCandidate Level.canonicalKacMoodyLevelReceipt
    ; p3ChernSimonsCandidateIsCanonical =
        refl
    ; finiteSU2LRow =
        Ledger.p3SU2LFinitePrimeLaneSMRow
    ; finiteSU2LRowIsCanonical =
        refl
    ; exactSMBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; conditionalGDHRSMPromotionReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; conditionalGDHRStatusStillFalse =
        Conditional.unconditionalGDHREqualsGSMPromotedIsFalse
          Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; chain =
        canonicalFermionLoopChain
    ; chainIsCanonical =
        refl
    ; conditions =
        canonicalFermionLoopConditions
    ; conditionsAreCanonical =
        refl
    ; shiftComputation =
        canonicalFermionicLoopLevelShiftComputation
    ; shiftComputationIsCanonical =
        refl
    ; su2FundamentalIndexRecorded =
        true
    ; su2FundamentalIndexRecordedIsTrue =
        refl
    ; twoDiracContributionRecorded =
        true
    ; twoDiracContributionRecordedIsTrue =
        refl
    ; fourWeylContributionRecorded =
        true
    ; fourWeylContributionRecordedIsTrue =
        refl
    ; kThreeToKEffOneCandidate =
        true
    ; kThreeToKEffOneCandidateIsTrue =
        refl
    ; exactSU2WeakDerivation =
        false
    ; exactSU2WeakDerivationIsFalse =
        refl
    ; exactSMReconstruction =
        false
    ; exactSMReconstructionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; residualBlockers =
        canonicalFermionLoopResidualBlockers
    ; residualBlockersAreCanonical =
        refl
    ; receiptBoundary =
        canonicalFermionLoopBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

fermionicLoopReceiptEffectiveLevelIsOne :
  effectiveLevel
    (shiftComputation canonicalFermionicLoopCSShiftReceipt)
  ≡
  1
fermionicLoopReceiptEffectiveLevelIsOne =
  refl

fermionicLoopReceiptExactSU2WeakDerivationFalse :
  exactSU2WeakDerivation canonicalFermionicLoopCSShiftReceipt
  ≡
  false
fermionicLoopReceiptExactSU2WeakDerivationFalse =
  refl

fermionicLoopReceiptExactSMReconstructionFalse :
  exactSMReconstruction canonicalFermionicLoopCSShiftReceipt
  ≡
  false
fermionicLoopReceiptExactSMReconstructionFalse =
  refl

fermionicLoopReceiptExactGDHREqualsGSMPromotionFalse :
  exactGDHREqualsGSMPromotion canonicalFermionicLoopCSShiftReceipt
  ≡
  false
fermionicLoopReceiptExactGDHREqualsGSMPromotionFalse =
  refl
