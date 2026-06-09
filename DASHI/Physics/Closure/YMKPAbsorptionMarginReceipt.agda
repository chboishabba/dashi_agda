module DASHI.Physics.Closure.YMKPAbsorptionMarginReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_; s≤s; z≤n)

open import MonsterOntos using (SSP; p7)

------------------------------------------------------------------------
-- YM KP absorption margin receipt.
--
-- This receipt is deliberately narrower than a KP convergence receipt.
-- It records the strict rho < 1 threshold needed for absorption, separates
-- convergence bookkeeping from absorption bookkeeping, and keeps the live
-- p = 7 beta threshold around 13.64 as a receipt-level rational/string fact.
--
-- No continuum Yang-Mills construction, no mass gap, and no Clay promotion
-- are made here.

data YMKPAbsorptionMarginStatus : Set where
  ymKPAbsorptionStrictRhoThresholdRecorded :
    YMKPAbsorptionMarginStatus

data YMKPConvergenceVerdict : Set where
  convergenceTailRecordedButNotAbsorption :
    YMKPConvergenceVerdict

data YMKPAbsorptionVerdict : Set where
  absorptionRequiresStrictRhoBelowOne :
    YMKPAbsorptionVerdict

data YMKPRhoThresholdStatus : Set where
  strictRhoLessThanOneThresholdClosed :
    YMKPRhoThresholdStatus

data YMKPBetaThresholdStatus : Set where
  liveP7BetaThresholdRecordedAsReceiptFact :
    YMKPBetaThresholdStatus

data YMKPAbsorptionOpenHardPart : Set where
  analyticAbsorptionFromConvergenceBridgeOpen :
    YMKPAbsorptionOpenHardPart

  physicalYMThresholdInterpretationOpen :
    YMKPAbsorptionOpenHardPart

canonicalYMKPAbsorptionOpenHardParts :
  List YMKPAbsorptionOpenHardPart
canonicalYMKPAbsorptionOpenHardParts =
  analyticAbsorptionFromConvergenceBridgeOpen
  ∷ physicalYMThresholdInterpretationOpen
  ∷ []

data YMKPAbsorptionNonClaim : Set where
  noConvergenceImpliesAbsorptionPromotion :
    YMKPAbsorptionNonClaim

  noContinuumYangMillsPromotion :
    YMKPAbsorptionNonClaim

  noMassGapPromotion :
    YMKPAbsorptionNonClaim

  noClayPromotion :
    YMKPAbsorptionNonClaim

canonicalYMKPAbsorptionNonClaims :
  List YMKPAbsorptionNonClaim
canonicalYMKPAbsorptionNonClaims =
  noConvergenceImpliesAbsorptionPromotion
  ∷ noContinuumYangMillsPromotion
  ∷ noMassGapPromotion
  ∷ noClayPromotion
  ∷ []

data YMKPAbsorptionPromotion : Set where

ymKPAbsorptionPromotionImpossibleHere :
  YMKPAbsorptionPromotion →
  ⊥
ymKPAbsorptionPromotionImpossibleHere ()

strictRhoNumerator :
  Nat
strictRhoNumerator =
  1

strictRhoDenominator :
  Nat
strictRhoDenominator =
  2

strictAbsorptionMarginNumerator :
  Nat
strictAbsorptionMarginNumerator =
  1

strictAbsorptionMarginDenominator :
  Nat
strictAbsorptionMarginDenominator =
  2

strictRhoBelowOne :
  strictRhoNumerator < strictRhoDenominator
strictRhoBelowOne =
  s≤s (s≤s z≤n)

p7BetaThresholdNumerator :
  Nat
p7BetaThresholdNumerator =
  341

p7BetaThresholdDenominator :
  Nat
p7BetaThresholdDenominator =
  25

p7BetaThresholdDecimal :
  String
p7BetaThresholdDecimal =
  "13.64"

p7BetaThresholdReading :
  String
p7BetaThresholdReading =
  "Live YM KP absorption lane fact: for p=7, beta threshold is recorded as approximately 13.64, represented here by 341/25."

convergenceVsAbsorptionReading :
  String
convergenceVsAbsorptionReading =
  "Convergence records a finite tail control surface; absorption records the strict rho < 1 deficit needed to absorb the retained term. This receipt does not identify the two."

record StrictRhoAbsorptionThreshold : Set where
  field
    rhoNumerator :
      Nat

    rhoNumeratorIsCanonical :
      rhoNumerator ≡ strictRhoNumerator

    rhoDenominator :
      Nat

    rhoDenominatorIsCanonical :
      rhoDenominator ≡ strictRhoDenominator

    rhoBelowOne :
      rhoNumerator < rhoDenominator

    absorptionMarginNumerator :
      Nat

    absorptionMarginNumeratorIsCanonical :
      absorptionMarginNumerator ≡ strictAbsorptionMarginNumerator

    absorptionMarginDenominator :
      Nat

    absorptionMarginDenominatorIsCanonical :
      absorptionMarginDenominator ≡ strictAbsorptionMarginDenominator

    marginPositive :
      absorptionMarginNumerator < absorptionMarginDenominator

    thresholdStatus :
      YMKPRhoThresholdStatus

    thresholdStatusIsClosed :
      thresholdStatus ≡ strictRhoLessThanOneThresholdClosed

open StrictRhoAbsorptionThreshold public

canonicalStrictRhoAbsorptionThreshold :
  StrictRhoAbsorptionThreshold
canonicalStrictRhoAbsorptionThreshold =
  record
    { rhoNumerator =
        strictRhoNumerator
    ; rhoNumeratorIsCanonical =
        refl
    ; rhoDenominator =
        strictRhoDenominator
    ; rhoDenominatorIsCanonical =
        refl
    ; rhoBelowOne =
        strictRhoBelowOne
    ; absorptionMarginNumerator =
        strictAbsorptionMarginNumerator
    ; absorptionMarginNumeratorIsCanonical =
        refl
    ; absorptionMarginDenominator =
        strictAbsorptionMarginDenominator
    ; absorptionMarginDenominatorIsCanonical =
        refl
    ; marginPositive =
        strictRhoBelowOne
    ; thresholdStatus =
        strictRhoLessThanOneThresholdClosed
    ; thresholdStatusIsClosed =
        refl
    }

record P7BetaThresholdReceiptFact : Set where
  field
    thresholdPrime :
      SSP

    thresholdPrimeIsP7 :
      thresholdPrime ≡ p7

    betaThresholdNumerator :
      Nat

    betaThresholdNumeratorIs341 :
      betaThresholdNumerator ≡ p7BetaThresholdNumerator

    betaThresholdDenominator :
      Nat

    betaThresholdDenominatorIs25 :
      betaThresholdDenominator ≡ p7BetaThresholdDenominator

    betaThresholdDecimalFact :
      String

    betaThresholdDecimalFactIs1364 :
      betaThresholdDecimalFact ≡ p7BetaThresholdDecimal

    betaThresholdStatus :
      YMKPBetaThresholdStatus

    betaThresholdStatusIsReceiptFact :
      betaThresholdStatus ≡ liveP7BetaThresholdRecordedAsReceiptFact

open P7BetaThresholdReceiptFact public

canonicalP7BetaThresholdReceiptFact :
  P7BetaThresholdReceiptFact
canonicalP7BetaThresholdReceiptFact =
  record
    { thresholdPrime =
        p7
    ; thresholdPrimeIsP7 =
        refl
    ; betaThresholdNumerator =
        p7BetaThresholdNumerator
    ; betaThresholdNumeratorIs341 =
        refl
    ; betaThresholdDenominator =
        p7BetaThresholdDenominator
    ; betaThresholdDenominatorIs25 =
        refl
    ; betaThresholdDecimalFact =
        p7BetaThresholdDecimal
    ; betaThresholdDecimalFactIs1364 =
        refl
    ; betaThresholdStatus =
        liveP7BetaThresholdRecordedAsReceiptFact
    ; betaThresholdStatusIsReceiptFact =
        refl
    }

record YMKPAbsorptionMarginReceipt : Setω where
  field
    status :
      YMKPAbsorptionMarginStatus

    statusIsCanonical :
      status ≡ ymKPAbsorptionStrictRhoThresholdRecorded

    convergenceVerdict :
      YMKPConvergenceVerdict

    convergenceVerdictIsSeparated :
      convergenceVerdict ≡ convergenceTailRecordedButNotAbsorption

    absorptionVerdict :
      YMKPAbsorptionVerdict

    absorptionVerdictIsStrictRhoGate :
      absorptionVerdict ≡ absorptionRequiresStrictRhoBelowOne

    strictRhoThreshold :
      StrictRhoAbsorptionThreshold

    strictRhoThresholdIsCanonical :
      strictRhoThreshold ≡ canonicalStrictRhoAbsorptionThreshold

    strictRhoThresholdClosed :
      thresholdStatus strictRhoThreshold
      ≡
      strictRhoLessThanOneThresholdClosed

    p7BetaThresholdFact :
      P7BetaThresholdReceiptFact

    p7BetaThresholdFactIsCanonical :
      p7BetaThresholdFact ≡ canonicalP7BetaThresholdReceiptFact

    p7BetaThresholdDecimalRecorded :
      betaThresholdDecimalFact p7BetaThresholdFact
      ≡
      p7BetaThresholdDecimal

    absorptionEstablishedAsReceiptThreshold :
      Bool

    absorptionEstablishedAsReceiptThresholdIsTrue :
      absorptionEstablishedAsReceiptThreshold ≡ true

    convergencePromotedToAbsorption :
      Bool

    convergencePromotedToAbsorptionIsFalse :
      convergencePromotedToAbsorption ≡ false

    openHardParts :
      List YMKPAbsorptionOpenHardPart

    openHardPartsAreCanonical :
      openHardParts ≡ canonicalYMKPAbsorptionOpenHardParts

    nonClaims :
      List YMKPAbsorptionNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMKPAbsorptionNonClaims

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    massGapPromoted :
      Bool

    massGapPromotedIsFalse :
      massGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotionFlags :
      List YMKPAbsorptionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    convergenceVsAbsorptionStatement :
      String

    convergenceVsAbsorptionStatementIsCanonical :
      convergenceVsAbsorptionStatement ≡ convergenceVsAbsorptionReading

    p7BetaThresholdStatement :
      String

    p7BetaThresholdStatementIsCanonical :
      p7BetaThresholdStatement ≡ p7BetaThresholdReading

    receiptBoundary :
      List String

open YMKPAbsorptionMarginReceipt public

canonicalYMKPAbsorptionMarginReceipt :
  YMKPAbsorptionMarginReceipt
canonicalYMKPAbsorptionMarginReceipt =
  record
    { status =
        ymKPAbsorptionStrictRhoThresholdRecorded
    ; statusIsCanonical =
        refl
    ; convergenceVerdict =
        convergenceTailRecordedButNotAbsorption
    ; convergenceVerdictIsSeparated =
        refl
    ; absorptionVerdict =
        absorptionRequiresStrictRhoBelowOne
    ; absorptionVerdictIsStrictRhoGate =
        refl
    ; strictRhoThreshold =
        canonicalStrictRhoAbsorptionThreshold
    ; strictRhoThresholdIsCanonical =
        refl
    ; strictRhoThresholdClosed =
        refl
    ; p7BetaThresholdFact =
        canonicalP7BetaThresholdReceiptFact
    ; p7BetaThresholdFactIsCanonical =
        refl
    ; p7BetaThresholdDecimalRecorded =
        refl
    ; absorptionEstablishedAsReceiptThreshold =
        true
    ; absorptionEstablishedAsReceiptThresholdIsTrue =
        refl
    ; convergencePromotedToAbsorption =
        false
    ; convergencePromotedToAbsorptionIsFalse =
        refl
    ; openHardParts =
        canonicalYMKPAbsorptionOpenHardParts
    ; openHardPartsAreCanonical =
        refl
    ; nonClaims =
        canonicalYMKPAbsorptionNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; massGapPromoted =
        false
    ; massGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; convergenceVsAbsorptionStatement =
        convergenceVsAbsorptionReading
    ; convergenceVsAbsorptionStatementIsCanonical =
        refl
    ; p7BetaThresholdStatement =
        p7BetaThresholdReading
    ; p7BetaThresholdStatementIsCanonical =
        refl
    ; receiptBoundary =
        "YM KP absorption margin only"
        ∷ "strict rho < 1 threshold is closed as the receipt-level absorption gate"
        ∷ "convergence is recorded separately and is not promoted to absorption"
        ∷ "live p=7 beta threshold is recorded as 341/25 ~= 13.64"
        ∷ "no continuum Yang-Mills, mass gap, or Clay promotion is made"
        ∷ []
    }

ymKPAbsorptionStrictRhoBelowOneClosed :
  rhoBelowOne
    (strictRhoThreshold canonicalYMKPAbsorptionMarginReceipt)
  ≡
  strictRhoBelowOne
ymKPAbsorptionStrictRhoBelowOneClosed =
  refl

ymKPConvergenceNotPromotedToAbsorption :
  convergencePromotedToAbsorption canonicalYMKPAbsorptionMarginReceipt
  ≡
  false
ymKPConvergenceNotPromotedToAbsorption =
  refl

ymKPP7BetaThresholdDecimalIs1364 :
  betaThresholdDecimalFact
    (p7BetaThresholdFact canonicalYMKPAbsorptionMarginReceipt)
  ≡
  "13.64"
ymKPP7BetaThresholdDecimalIs1364 =
  refl

ymKPAbsorptionNoClayPromotion :
  clayYangMillsPromoted canonicalYMKPAbsorptionMarginReceipt ≡ false
ymKPAbsorptionNoClayPromotion =
  refl
