module DASHI.Physics.Closure.YMCharacterExpansionContinuumReformulationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMBetaBridgeQuantitativeGapReceipt as Gap
import DASHI.Physics.Closure.YMBalabanPhysicalBetaBridgeTargetReceipt
  as Target

------------------------------------------------------------------------
-- YM character-expansion continuum-limit reformulation.
--
-- The transfer-matrix/character-expansion calculation gives a positive mass
-- gap in lattice units for each fixed beta:
--
--   m_latt(beta) >= -2 log(I_1(beta) / I_0(beta)) > 0.
--
-- At beta = 6 this gives m_latt >= 0.183; at beta = 12.97 it gives
-- m_latt >= 0.080.  Therefore the physical blocker is not fixed-lattice
-- positivity.  The Clay issue is whether the gap survives the continuum
-- limit, i.e. whether m_latt(beta) combined with the lattice spacing scale
-- leaves a nonzero physical mass as a(beta) -> 0 and beta -> infinity.

data YMCharacterExpansionReformulationStatus : Set where
  fixedLatticeMassPositive_continuumSurvivalOpen :
    YMCharacterExpansionReformulationStatus

data YMCharacterExpansionResult : Set where
  transferMatrixGivesPositiveFixedBetaLatticeGap :
    YMCharacterExpansionResult

  betaSixLatticeMassLowerBoundRecorded :
    YMCharacterExpansionResult

  betaTwelveNinetySevenLatticeMassLowerBoundRecorded :
    YMCharacterExpansionResult

  characterBoundVanishesAsBetaGoesToInfinity :
    YMCharacterExpansionResult

  clayQuestionIsContinuumSurvival :
    YMCharacterExpansionResult

canonicalYMCharacterExpansionResults :
  List YMCharacterExpansionResult
canonicalYMCharacterExpansionResults =
  transferMatrixGivesPositiveFixedBetaLatticeGap
  ∷ betaSixLatticeMassLowerBoundRecorded
  ∷ betaTwelveNinetySevenLatticeMassLowerBoundRecorded
  ∷ characterBoundVanishesAsBetaGoesToInfinity
  ∷ clayQuestionIsContinuumSurvival
  ∷ []

data YMContinuumSurvivalObligation : Set where
  controlProductOfLatticeGapAndScale :
    YMContinuumSurvivalObligation

  proveNonzeroPhysicalLambdaInContinuumLimit :
    YMContinuumSurvivalObligation

  controlPolymerCorrectionsAlongBetaToInfinity :
    YMContinuumSurvivalObligation

  preserveOSPositivityInTheLimit :
    YMContinuumSurvivalObligation

canonicalYMContinuumSurvivalObligations :
  List YMContinuumSurvivalObligation
canonicalYMContinuumSurvivalObligations =
  controlProductOfLatticeGapAndScale
  ∷ proveNonzeroPhysicalLambdaInContinuumLimit
  ∷ controlPolymerCorrectionsAlongBetaToInfinity
  ∷ preserveOSPositivityInTheLimit
  ∷ []

data YMCharacterExpansionPromotion : Set where

ymCharacterExpansionPromotionImpossibleHere :
  YMCharacterExpansionPromotion →
  ⊥
ymCharacterExpansionPromotionImpossibleHere ()

betaSixHundredths :
  Nat
betaSixHundredths =
  600

betaStrictHundredths :
  Nat
betaStrictHundredths =
  1297

mLattBetaSixThousandths :
  Nat
mLattBetaSixThousandths =
  183

mLattBetaStrictThousandths :
  Nat
mLattBetaStrictThousandths =
  80

characterExpansionStatement :
  String
characterExpansionStatement =
  "The character-expansion transfer-matrix bound gives m_latt(beta) >= -2 log(I1(beta)/I0(beta)) > 0 at fixed lattice spacing; beta=6 gives about 0.183 and beta=12.97 gives about 0.080 in lattice units."

continuumReformulationStatement :
  String
continuumReformulationStatement =
  "The YM Clay blocker is continuum survival, not fixed-lattice positivity: the bound weakens as beta -> infinity, so one must prove the physical gap survives the a(beta)->0 limit."

promotionBoundary :
  String
promotionBoundary =
  "This receipt reformulates the beta bridge.  It does not prove continuum Yang-Mills, survival of m_latt*a(beta), the physical mass gap, or Clay Yang-Mills."

record YMCharacterExpansionContinuumReformulationReceipt : Setω where
  field
    status :
      YMCharacterExpansionReformulationStatus

    statusIsCanonical :
      status ≡ fixedLatticeMassPositive_continuumSurvivalOpen

    quantitativeGapReceipt :
      Gap.YMBetaBridgeQuantitativeGapReceipt

    quantitativeGapNonperturbative :
      Gap.nonperturbativeInputRequired quantitativeGapReceipt ≡ true

    quantitativeGapNoClay :
      Gap.clayYMPromoted quantitativeGapReceipt ≡ false

    bridgeTargetReceipt :
      Target.YMBalabanPhysicalBetaBridgeTargetReceipt

    bridgeTargetStillOpen :
      Target.physicalBetaBridgeProvedHere bridgeTargetReceipt ≡ false

    bridgeTargetNoContinuum :
      Target.continuumYangMillsPromoted bridgeTargetReceipt ≡ false

    bridgeTargetNoClay :
      Target.clayYangMillsPromoted bridgeTargetReceipt ≡ false

    results :
      List YMCharacterExpansionResult

    resultsAreCanonical :
      results ≡ canonicalYMCharacterExpansionResults

    continuumObligations :
      List YMContinuumSurvivalObligation

    continuumObligationsAreCanonical :
      continuumObligations ≡ canonicalYMContinuumSurvivalObligations

    betaSix :
      Nat

    betaSixIs600 :
      betaSix ≡ betaSixHundredths

    betaStrict :
      Nat

    betaStrictIs1297 :
      betaStrict ≡ betaStrictHundredths

    mLattAtBetaSix :
      Nat

    mLattAtBetaSixIs0183 :
      mLattAtBetaSix ≡ mLattBetaSixThousandths

    mLattAtBetaStrict :
      Nat

    mLattAtBetaStrictIs0080 :
      mLattAtBetaStrict ≡ mLattBetaStrictThousandths

    fixedLatticeMassPositiveRecorded :
      Bool

    fixedLatticeMassPositiveRecordedIsTrue :
      fixedLatticeMassPositiveRecorded ≡ true

    continuumSurvivalProvedHere :
      Bool

    continuumSurvivalProvedHereIsFalse :
      continuumSurvivalProvedHere ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    promotions :
      List YMCharacterExpansionPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      YMCharacterExpansionPromotion →
      ⊥

    characterExpansionText :
      String

    characterExpansionTextIsCanonical :
      characterExpansionText ≡ characterExpansionStatement

    continuumReformulationText :
      String

    continuumReformulationTextIsCanonical :
      continuumReformulationText ≡ continuumReformulationStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open YMCharacterExpansionContinuumReformulationReceipt public

canonicalYMCharacterExpansionContinuumReformulationReceipt :
  YMCharacterExpansionContinuumReformulationReceipt
canonicalYMCharacterExpansionContinuumReformulationReceipt =
  record
    { status =
        fixedLatticeMassPositive_continuumSurvivalOpen
    ; statusIsCanonical =
        refl
    ; quantitativeGapReceipt =
        Gap.canonicalYMBetaBridgeQuantitativeGapReceipt
    ; quantitativeGapNonperturbative =
        refl
    ; quantitativeGapNoClay =
        refl
    ; bridgeTargetReceipt =
        Target.canonicalYMBalabanPhysicalBetaBridgeTargetReceipt
    ; bridgeTargetStillOpen =
        refl
    ; bridgeTargetNoContinuum =
        refl
    ; bridgeTargetNoClay =
        refl
    ; results =
        canonicalYMCharacterExpansionResults
    ; resultsAreCanonical =
        refl
    ; continuumObligations =
        canonicalYMContinuumSurvivalObligations
    ; continuumObligationsAreCanonical =
        refl
    ; betaSix =
        betaSixHundredths
    ; betaSixIs600 =
        refl
    ; betaStrict =
        betaStrictHundredths
    ; betaStrictIs1297 =
        refl
    ; mLattAtBetaSix =
        mLattBetaSixThousandths
    ; mLattAtBetaSixIs0183 =
        refl
    ; mLattAtBetaStrict =
        mLattBetaStrictThousandths
    ; mLattAtBetaStrictIs0080 =
        refl
    ; fixedLatticeMassPositiveRecorded =
        true
    ; fixedLatticeMassPositiveRecordedIsTrue =
        refl
    ; continuumSurvivalProvedHere =
        false
    ; continuumSurvivalProvedHereIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        ymCharacterExpansionPromotionImpossibleHere
    ; characterExpansionText =
        characterExpansionStatement
    ; characterExpansionTextIsCanonical =
        refl
    ; continuumReformulationText =
        continuumReformulationStatement
    ; continuumReformulationTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalYMCharacterExpansionFixedLatticeGapRecorded :
  fixedLatticeMassPositiveRecorded
    canonicalYMCharacterExpansionContinuumReformulationReceipt
  ≡
  true
canonicalYMCharacterExpansionFixedLatticeGapRecorded =
  refl

canonicalYMCharacterExpansionNoClay :
  clayYMPromoted canonicalYMCharacterExpansionContinuumReformulationReceipt
  ≡
  false
canonicalYMCharacterExpansionNoClay =
  refl
