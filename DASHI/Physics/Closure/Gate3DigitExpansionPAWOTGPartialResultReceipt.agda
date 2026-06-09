module DASHI.Physics.Closure.Gate3DigitExpansionPAWOTGPartialResultReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3AdelicLocalizationReductionReceipt
  as Localization
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt
  as Target

------------------------------------------------------------------------
-- Digit-expansion PAWOTG partial result.
--
-- This receipt records the new concrete positive result for the Gate 3
-- PAWOTG lane.  The digit-expansion map
--
--   phi_digit(sum a_k p^k) = sum a_k p^(-k-1)
--
-- sends the uniform p-adic digit cylinder to an Archimedean interval with
-- variance 1/12, independent of p.  Hence the spread
-- sigma = 1/sqrt(12) ~= 0.2887 is below the current p=3 PAWOTG threshold
-- sigma_crit = 0.5052.  At BT level j the spread shrinks by p^{-j}.
--
-- This proves achievability of the PAWOTG spread target for a natural
-- embedding.  It does not prove that the specific SSP/CM atom dictionary uses
-- this embedding or that the Hecke/inert-prime embedding has the same spread.

data Gate3DigitExpansionPAWOTGStatus : Set where
  digitExpansionEmbeddingSatisfiesPAWOTGThreshold_partialResult :
    Gate3DigitExpansionPAWOTGStatus

data DigitExpansionComputationStep : Set where
  uniformDigitsHaveVarianceP2Minus1Over12 :
    DigitExpansionComputationStep

  geometricPAdicScaleSumCancelsPDependence :
    DigitExpansionComputationStep

  varianceEqualsOneTwelfthForEveryPrime :
    DigitExpansionComputationStep

  sigmaEqualsOneOverSqrtTwelve :
    DigitExpansionComputationStep

  levelJSpreadShrinksByPToMinusJ :
    DigitExpansionComputationStep

canonicalDigitExpansionComputation :
  List DigitExpansionComputationStep
canonicalDigitExpansionComputation =
  uniformDigitsHaveVarianceP2Minus1Over12
  ∷ geometricPAdicScaleSumCancelsPDependence
  ∷ varianceEqualsOneTwelfthForEveryPrime
  ∷ sigmaEqualsOneOverSqrtTwelve
  ∷ levelJSpreadShrinksByPToMinusJ
  ∷ []

data DigitExpansionConclusion : Set where
  pawotgThresholdAchievableInPrinciple :
    DigitExpansionConclusion

  kozyrevP2HaarCaseIsDigitExpansionModel :
    DigitExpansionConclusion

  allPrimesPassSpreadThresholdForPhiDigit :
    DigitExpansionConclusion

  pAdicLevelRefinementImprovesSpread :
    DigitExpansionConclusion

canonicalDigitExpansionConclusions :
  List DigitExpansionConclusion
canonicalDigitExpansionConclusions =
  pawotgThresholdAchievableInPrinciple
  ∷ kozyrevP2HaarCaseIsDigitExpansionModel
  ∷ allPrimesPassSpreadThresholdForPhiDigit
  ∷ pAdicLevelRefinementImprovesSpread
  ∷ []

data DigitExpansionRemainingGap : Set where
  sspAtomEmbeddingMayNotBePhiDigit :
    DigitExpansionRemainingGap

  heckeCharacterEmbeddingMayChangeSpread :
    DigitExpansionRemainingGap

  inertPrimeCMAtomsNeedSeparateAudit :
    DigitExpansionRemainingGap

  uniformFrameLowerBoundStillNeedsSSPEmbedding :
    DigitExpansionRemainingGap

canonicalDigitExpansionRemainingGaps :
  List DigitExpansionRemainingGap
canonicalDigitExpansionRemainingGaps =
  sspAtomEmbeddingMayNotBePhiDigit
  ∷ heckeCharacterEmbeddingMayChangeSpread
  ∷ inertPrimeCMAtomsNeedSeparateAudit
  ∷ uniformFrameLowerBoundStillNeedsSSPEmbedding
  ∷ []

data Gate3DigitExpansionPromotion : Set where

gate3DigitExpansionPromotionImpossibleHere :
  Gate3DigitExpansionPromotion →
  ⊥
gate3DigitExpansionPromotionImpossibleHere ()

varianceDenominator :
  Nat
varianceDenominator =
  12

sigmaDigitTenThousandths :
  Nat
sigmaDigitTenThousandths =
  2887

sigmaCritP3TenThousandths :
  Nat
sigmaCritP3TenThousandths =
  5052

bindingPrime :
  Nat
bindingPrime =
  3

digitExpansionStatement :
  String
digitExpansionStatement =
  "For phi_digit, Var(sum x_k p^{-k}) = 1/12 for every prime p, so sigma = 1/sqrt(12) ~= 0.2887 < 0.5052; at BT level j the spread is p^{-j}/sqrt(12)."

remainingGapStatement :
  String
remainingGapStatement =
  "This is a genuine PAWOTG partial result and achievability proof.  The remaining Gate 3 gap is proving that the actual SSP/CM/Hecke atom embedding is phi_digit or has the same uniform spread."

promotionBoundary :
  String
promotionBoundary =
  "The digit-expansion calculation does not prove inf_N A_N > 0 for the SSP atom dictionary, Mosco recovery, no spectral pollution, Gate 3 closure, or Clay promotion."

record Gate3DigitExpansionPAWOTGPartialResultReceipt : Setω where
  field
    status :
      Gate3DigitExpansionPAWOTGStatus

    statusIsCanonical :
      status
      ≡
      digitExpansionEmbeddingSatisfiesPAWOTGThreshold_partialResult

    localizationReceipt :
      Localization.Gate3AdelicLocalizationReductionReceipt

    localizationUniformSeparationStillOpen :
      Localization.uniformSeparationProvedHere localizationReceipt
      ≡
      false

    targetReceipt :
      Target.Gate3PAWOTGUniformSeparationTargetReceipt

    targetInfANStillOpen :
      Target.infANPositiveProvedHere targetReceipt ≡ false

    targetGate3StillFalse :
      Target.gate3Promoted targetReceipt ≡ false

    computationSteps :
      List DigitExpansionComputationStep

    computationStepsAreCanonical :
      computationSteps ≡ canonicalDigitExpansionComputation

    conclusions :
      List DigitExpansionConclusion

    conclusionsAreCanonical :
      conclusions ≡ canonicalDigitExpansionConclusions

    remainingGaps :
      List DigitExpansionRemainingGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalDigitExpansionRemainingGaps

    varianceDenominatorRecorded :
      Nat

    varianceDenominatorIs12 :
      varianceDenominatorRecorded ≡ varianceDenominator

    sigmaDigit :
      Nat

    sigmaDigitIs02887 :
      sigmaDigit ≡ sigmaDigitTenThousandths

    sigmaCritP3 :
      Nat

    sigmaCritP3Is05052 :
      sigmaCritP3 ≡ sigmaCritP3TenThousandths

    bindingPrimeRecorded :
      Nat

    bindingPrimeRecordedIsP3 :
      bindingPrimeRecorded ≡ bindingPrime

    phiDigitPassesPAWOTGThreshold :
      Bool

    phiDigitPassesPAWOTGThresholdIsTrue :
      phiDigitPassesPAWOTGThreshold ≡ true

    sspEmbeddingIdentifiedWithPhiDigit :
      Bool

    sspEmbeddingIdentifiedWithPhiDigitIsFalse :
      sspEmbeddingIdentifiedWithPhiDigit ≡ false

    uniformFrameLowerBoundProvedHere :
      Bool

    uniformFrameLowerBoundProvedHereIsFalse :
      uniformFrameLowerBoundProvedHere ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List Gate3DigitExpansionPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3DigitExpansionPromotion →
      ⊥

    statement :
      String

    statementIsCanonical :
      statement ≡ digitExpansionStatement

    gap :
      String

    gapIsCanonical :
      gap ≡ remainingGapStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open Gate3DigitExpansionPAWOTGPartialResultReceipt public

canonicalGate3DigitExpansionPAWOTGPartialResultReceipt :
  Gate3DigitExpansionPAWOTGPartialResultReceipt
canonicalGate3DigitExpansionPAWOTGPartialResultReceipt =
  record
    { status =
        digitExpansionEmbeddingSatisfiesPAWOTGThreshold_partialResult
    ; statusIsCanonical =
        refl
    ; localizationReceipt =
        Localization.canonicalGate3AdelicLocalizationReductionReceipt
    ; localizationUniformSeparationStillOpen =
        refl
    ; targetReceipt =
        Target.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; targetInfANStillOpen =
        refl
    ; targetGate3StillFalse =
        refl
    ; computationSteps =
        canonicalDigitExpansionComputation
    ; computationStepsAreCanonical =
        refl
    ; conclusions =
        canonicalDigitExpansionConclusions
    ; conclusionsAreCanonical =
        refl
    ; remainingGaps =
        canonicalDigitExpansionRemainingGaps
    ; remainingGapsAreCanonical =
        refl
    ; varianceDenominatorRecorded =
        varianceDenominator
    ; varianceDenominatorIs12 =
        refl
    ; sigmaDigit =
        sigmaDigitTenThousandths
    ; sigmaDigitIs02887 =
        refl
    ; sigmaCritP3 =
        sigmaCritP3TenThousandths
    ; sigmaCritP3Is05052 =
        refl
    ; bindingPrimeRecorded =
        bindingPrime
    ; bindingPrimeRecordedIsP3 =
        refl
    ; phiDigitPassesPAWOTGThreshold =
        true
    ; phiDigitPassesPAWOTGThresholdIsTrue =
        refl
    ; sspEmbeddingIdentifiedWithPhiDigit =
        false
    ; sspEmbeddingIdentifiedWithPhiDigitIsFalse =
        refl
    ; uniformFrameLowerBoundProvedHere =
        false
    ; uniformFrameLowerBoundProvedHereIsFalse =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3DigitExpansionPromotionImpossibleHere
    ; statement =
        digitExpansionStatement
    ; statementIsCanonical =
        refl
    ; gap =
        remainingGapStatement
    ; gapIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalPhiDigitPassesThreshold :
  phiDigitPassesPAWOTGThreshold
    canonicalGate3DigitExpansionPAWOTGPartialResultReceipt
  ≡
  true
canonicalPhiDigitPassesThreshold =
  refl

canonicalDigitExpansionNoGate3Promotion :
  gate3Promoted canonicalGate3DigitExpansionPAWOTGPartialResultReceipt
  ≡
  false
canonicalDigitExpansionNoGate3Promotion =
  refl
