module DASHI.Physics.Closure.Gate3NestingTaperConditionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3AtomSamplerPAWOTGQualityReceipt
  as Sampler
import DASHI.Physics.Closure.Gate3DigitExpansionPAWOTGPartialResultReceipt
  as Digit
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt
  as Target

------------------------------------------------------------------------
-- Gate 3 nesting/taper correction.
--
-- The latest BT-level calculation corrects the prior sampler diagnosis.
-- Kozyrev wavelets are mutually orthogonal in L2(Q_p): the p-adic Gram
-- matrix is the identity, with A_N = B_N = 1 and mu_N = 0.  The observed
-- finite-frame clustering came from the Archimedean inner-product model after
-- digit expansion, where parent-child supports are nested.  PAWOTG is the
-- condition that the Archimedean Gaussian taper damps this nesting leakage.

data Gate3NestingTaperConditionStatus : Set where
  gate3NestingTaperConditionRecorded_noPromotion :
    Gate3NestingTaperConditionStatus

data NestingTaperFact : Set where
  kozyrevWaveletsOrthogonalInQpL2 :
    NestingTaperFact

  pAdicGramMatrixIdentity :
    NestingTaperFact

  archimedeanDigitImageHasNestedSupports :
    NestingTaperFact

  parentChildNestingConstantPToMinusHalf :
    NestingTaperFact

  gaussianTaperDampsNestingLeakage :
    NestingTaperFact

  pawotgSeriesIsNestingTaperCriterion :
    NestingTaperFact

  digitExpansionBelowStrictP3Taper :
    NestingTaperFact

  pawotgSeriesAtDigitSigmaHasHeadroom :
    NestingTaperFact

canonicalNestingTaperFacts :
  List NestingTaperFact
canonicalNestingTaperFacts =
  kozyrevWaveletsOrthogonalInQpL2
  ∷ pAdicGramMatrixIdentity
  ∷ archimedeanDigitImageHasNestedSupports
  ∷ parentChildNestingConstantPToMinusHalf
  ∷ gaussianTaperDampsNestingLeakage
  ∷ pawotgSeriesIsNestingTaperCriterion
  ∷ digitExpansionBelowStrictP3Taper
  ∷ pawotgSeriesAtDigitSigmaHasHeadroom
  ∷ []

data NestingTaperOpenObligation : Set where
  proveSSPHeckeEmbeddingHasSameTaper :
    NestingTaperOpenObligation

  proveGaussianTaperConditionUniformInDepth :
    NestingTaperOpenObligation

  proveSSPEmbeddingSpreadBelowP3Taper :
    NestingTaperOpenObligation

  transferTaperConditionToUniformFrameLowerBound :
    NestingTaperOpenObligation

  transferUniformFrameToMoscoAndNoPollution :
    NestingTaperOpenObligation

canonicalNestingTaperOpenObligations :
  List NestingTaperOpenObligation
canonicalNestingTaperOpenObligations =
  proveSSPHeckeEmbeddingHasSameTaper
  ∷ proveGaussianTaperConditionUniformInDepth
  ∷ proveSSPEmbeddingSpreadBelowP3Taper
  ∷ transferTaperConditionToUniformFrameLowerBound
  ∷ transferUniformFrameToMoscoAndNoPollution
  ∷ []

data Gate3NestingTaperPromotion : Set where

gate3NestingTaperPromotionImpossibleHere :
  Gate3NestingTaperPromotion →
  ⊥
gate3NestingTaperPromotionImpossibleHere ()

pAdicGramLowerBound :
  Nat
pAdicGramLowerBound =
  1

pAdicGramUpperBound :
  Nat
pAdicGramUpperBound =
  1

pAdicMuNumerator :
  Nat
pAdicMuNumerator =
  0

sigmaDigitTenThousandths :
  Nat
sigmaDigitTenThousandths =
  2887

sigmaDigitMillionths :
  Nat
sigmaDigitMillionths =
  288675

sigmaTaperP3Millionths :
  Nat
sigmaTaperP3Millionths =
  318022

sigmaCritP3TenThousandths :
  Nat
sigmaCritP3TenThousandths =
  5052

pawotgSeriesAtDigitTenThousandths :
  Nat
pawotgSeriesAtDigitTenThousandths =
  803

bindingPrime :
  Nat
bindingPrime =
  3

nestingCorrectionStatement :
  String
nestingCorrectionStatement =
  "Gate3 correction: Kozyrev wavelets are orthogonal in L2(Q_p), so the p-adic Gram is identity.  The finite-frame failure came from Archimedean digit-image nesting, not from bad p-adic atoms."

taperConditionStatement :
  String
taperConditionStatement =
  "PAWOTG is the Gaussian taper condition that damps parent-child nesting leakage in the Archimedean image; the digit-expansion sigma=1/sqrt(12) ~= 0.288675 is below the stricter p=3 nesting taper 0.318022 and the PAWOTG series threshold 0.5052."

digitHeadroomStatement :
  String
digitHeadroomStatement =
  "At sigma_digit ~= 0.288675 the full p=3 PAWOTG series is about 0.0803, so the digit-expansion embedding has headroom; the open theorem is proving the actual SSP/Hecke embedding spread is below 0.318022."

promotionBoundary :
  String
promotionBoundary =
  "This receipt records the nesting/taper correction only.  It does not prove that the SSP/Hecke embedding has the taper, inf_N A_N > 0, Gate 3 closure, or Clay."

record Gate3NestingTaperConditionReceipt : Setω where
  field
    status :
      Gate3NestingTaperConditionStatus

    statusIsCanonical :
      status ≡ gate3NestingTaperConditionRecorded_noPromotion

    digitExpansionReceipt :
      Digit.Gate3DigitExpansionPAWOTGPartialResultReceipt

    digitExpansionPassesThreshold :
      Digit.phiDigitPassesPAWOTGThreshold digitExpansionReceipt ≡ true

    samplerReceipt :
      Sampler.Gate3AtomSamplerPAWOTGQualityReceipt

    priorSamplerDiagnosticNoPromotion :
      Sampler.gate3Promoted samplerReceipt ≡ false

    uniformSeparationTarget :
      Target.Gate3PAWOTGUniformSeparationTargetReceipt

    targetInfANPromoted :
      Target.infANPositiveProvedHere uniformSeparationTarget ≡ true

    facts :
      List NestingTaperFact

    factsAreCanonical :
      facts ≡ canonicalNestingTaperFacts

    openObligations :
      List NestingTaperOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalNestingTaperOpenObligations

    pAdicAN :
      Nat

    pAdicANIsOne :
      pAdicAN ≡ pAdicGramLowerBound

    pAdicBN :
      Nat

    pAdicBNIsOne :
      pAdicBN ≡ pAdicGramUpperBound

    pAdicMu :
      Nat

    pAdicMuIsZero :
      pAdicMu ≡ pAdicMuNumerator

    sigmaDigit :
      Nat

    sigmaDigitIs02887 :
      sigmaDigit ≡ sigmaDigitTenThousandths

    sigmaDigitPrecise :
      Nat

    sigmaDigitPreciseIs0288675 :
      sigmaDigitPrecise ≡ sigmaDigitMillionths

    sigmaTaperP3 :
      Nat

    sigmaTaperP3Is0318022 :
      sigmaTaperP3 ≡ sigmaTaperP3Millionths

    sigmaCritP3 :
      Nat

    sigmaCritP3Is05052 :
      sigmaCritP3 ≡ sigmaCritP3TenThousandths

    pawotgAtSigmaDigit :
      Nat

    pawotgAtSigmaDigitIs00803 :
      pawotgAtSigmaDigit ≡ pawotgSeriesAtDigitTenThousandths

    bindingPrimeRecorded :
      Nat

    bindingPrimeRecordedIsP3 :
      bindingPrimeRecorded ≡ bindingPrime

    priorSamplerWasRootProblem :
      Bool

    priorSamplerWasRootProblemIsFalse :
      priorSamplerWasRootProblem ≡ false

    archimedeanNestingIsRootProblem :
      Bool

    archimedeanNestingIsRootProblemIsTrue :
      archimedeanNestingIsRootProblem ≡ true

    digitExpansionTaperPasses :
      Bool

    digitExpansionTaperPassesIsTrue :
      digitExpansionTaperPasses ≡ true

    digitExpansionBelowStrictTaper :
      Bool

    digitExpansionBelowStrictTaperIsTrue :
      digitExpansionBelowStrictTaper ≡ true

    sspHeckeTaperProvedHere :
      Bool

    sspHeckeTaperProvedHereIsFalse :
      sspHeckeTaperProvedHere ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List Gate3NestingTaperPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3NestingTaperPromotion →
      ⊥

    correctionText :
      String

    correctionTextIsCanonical :
      correctionText ≡ nestingCorrectionStatement

    taperText :
      String

    taperTextIsCanonical :
      taperText ≡ taperConditionStatement

    digitHeadroomText :
      String

    digitHeadroomTextIsCanonical :
      digitHeadroomText ≡ digitHeadroomStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open Gate3NestingTaperConditionReceipt public

canonicalGate3NestingTaperConditionReceipt :
  Gate3NestingTaperConditionReceipt
canonicalGate3NestingTaperConditionReceipt =
  record
    { status =
        gate3NestingTaperConditionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; digitExpansionReceipt =
        Digit.canonicalGate3DigitExpansionPAWOTGPartialResultReceipt
    ; digitExpansionPassesThreshold =
        refl
    ; samplerReceipt =
        Sampler.canonicalGate3AtomSamplerPAWOTGQualityReceipt
    ; priorSamplerDiagnosticNoPromotion =
        refl
    ; uniformSeparationTarget =
        Target.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; targetInfANPromoted =
        refl
    ; facts =
        canonicalNestingTaperFacts
    ; factsAreCanonical =
        refl
    ; openObligations =
        canonicalNestingTaperOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; pAdicAN =
        pAdicGramLowerBound
    ; pAdicANIsOne =
        refl
    ; pAdicBN =
        pAdicGramUpperBound
    ; pAdicBNIsOne =
        refl
    ; pAdicMu =
        pAdicMuNumerator
    ; pAdicMuIsZero =
        refl
    ; sigmaDigit =
        sigmaDigitTenThousandths
    ; sigmaDigitIs02887 =
        refl
    ; sigmaDigitPrecise =
        sigmaDigitMillionths
    ; sigmaDigitPreciseIs0288675 =
        refl
    ; sigmaTaperP3 =
        sigmaTaperP3Millionths
    ; sigmaTaperP3Is0318022 =
        refl
    ; sigmaCritP3 =
        sigmaCritP3TenThousandths
    ; sigmaCritP3Is05052 =
        refl
    ; pawotgAtSigmaDigit =
        pawotgSeriesAtDigitTenThousandths
    ; pawotgAtSigmaDigitIs00803 =
        refl
    ; bindingPrimeRecorded =
        bindingPrime
    ; bindingPrimeRecordedIsP3 =
        refl
    ; priorSamplerWasRootProblem =
        false
    ; priorSamplerWasRootProblemIsFalse =
        refl
    ; archimedeanNestingIsRootProblem =
        true
    ; archimedeanNestingIsRootProblemIsTrue =
        refl
    ; digitExpansionTaperPasses =
        true
    ; digitExpansionTaperPassesIsTrue =
        refl
    ; digitExpansionBelowStrictTaper =
        true
    ; digitExpansionBelowStrictTaperIsTrue =
        refl
    ; sspHeckeTaperProvedHere =
        false
    ; sspHeckeTaperProvedHereIsFalse =
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
        gate3NestingTaperPromotionImpossibleHere
    ; correctionText =
        nestingCorrectionStatement
    ; correctionTextIsCanonical =
        refl
    ; taperText =
        taperConditionStatement
    ; taperTextIsCanonical =
        refl
    ; digitHeadroomText =
        digitHeadroomStatement
    ; digitHeadroomTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalGate3NestingRootIsArchimedean :
  archimedeanNestingIsRootProblem canonicalGate3NestingTaperConditionReceipt
  ≡
  true
canonicalGate3NestingRootIsArchimedean =
  refl

canonicalGate3NestingNoPromotion :
  gate3Promoted canonicalGate3NestingTaperConditionReceipt ≡ false
canonicalGate3NestingNoPromotion =
  refl
