module DASHI.Physics.Closure.CMCorrectionToT13Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23FromT13HeckeReceipt as T13

------------------------------------------------------------------------
-- CM-specialisation arithmetic for T13.
--
-- Quadratic-residue checks at p=13:
--   (-3/13) = +1, since 10 is a square mod 13.
--   (-7/13) = -1, since 6 is not a square mod 13.
--   (21/13) = -1, since 8 is not a square mod 13.
--
-- Thus 13 splits in Q(sqrt(-3)), is inert in Q(sqrt(-7)), and is inert in
-- the real quadratic subfield Q(sqrt(21)).  This receipt records the
-- arithmetic needed by the CM-correction lane and keeps the correction itself
-- diagnostic/open.

data QuadraticPrimeStatus : Set where
  split :
    QuadraticPrimeStatus

  inert :
    QuadraticPrimeStatus

data CMCorrectionToT13Status : Set where
  t13CMSplittingArithmeticRecorded :
    CMCorrectionToT13Status

data CMCorrectionToT13Blocker : Set where
  correctedCMIsogenyCountNotDerived :
    CMCorrectionToT13Blocker

  mixedSplitInertBehaviourRequiresBiquadraticCount :
    CMCorrectionToT13Blocker

  physicalCKMInterpretationNotBound :
    CMCorrectionToT13Blocker

  residualClosureNotDerived :
    CMCorrectionToT13Blocker

canonicalCMCorrectionToT13Blockers :
  List CMCorrectionToT13Blocker
canonicalCMCorrectionToT13Blockers =
  correctedCMIsogenyCountNotDerived
  ∷ mixedSplitInertBehaviourRequiresBiquadraticCount
  ∷ physicalCKMInterpretationNotBound
  ∷ residualClosureNotDerived
  ∷ []

data CMCorrectionToT13Promotion : Set where

cmCorrectionToT13PromotionImpossibleHere :
  CMCorrectionToT13Promotion →
  ⊥
cmCorrectionToT13PromotionImpossibleHere ()

record CMCorrectionToT13Receipt : Setω where
  field
    status :
      CMCorrectionToT13Status

    t13BaseReceipt :
      T13.Deg23FromT13HeckeReceipt

    t13BaseReceiptCanonical :
      Bool

    t13BaseReceiptCanonicalIsTrue :
      t13BaseReceiptCanonical ≡ true

    prime :
      Nat

    primeIsThirteen :
      prime ≡ 13

    minusThreeResidue :
      Nat

    minusThreeResidueIsTen :
      minusThreeResidue ≡ 10

    tenIsSquareModThirteen :
      Bool

    tenIsSquareModThirteenIsTrue :
      tenIsSquareModThirteen ≡ true

    legendreMinusThreeOverThirteen :
      String

    legendreMinusThreeOverThirteenIsPlusOne :
      legendreMinusThreeOverThirteen ≡ "(-3/13)=+1"

    qsqrtMinusThreeStatus :
      QuadraticPrimeStatus

    qsqrtMinusThreeStatusIsSplit :
      qsqrtMinusThreeStatus ≡ split

    minusSevenResidue :
      Nat

    minusSevenResidueIsSix :
      minusSevenResidue ≡ 6

    sixIsSquareModThirteen :
      Bool

    sixIsSquareModThirteenIsFalse :
      sixIsSquareModThirteen ≡ false

    legendreMinusSevenOverThirteen :
      String

    legendreMinusSevenOverThirteenIsMinusOne :
      legendreMinusSevenOverThirteen ≡ "(-7/13)=-1"

    qsqrtMinusSevenStatus :
      QuadraticPrimeStatus

    qsqrtMinusSevenStatusIsInert :
      qsqrtMinusSevenStatus ≡ inert

    twentyOneResidue :
      Nat

    twentyOneResidueIsEight :
      twentyOneResidue ≡ 8

    eightIsSquareModThirteen :
      Bool

    eightIsSquareModThirteenIsFalse :
      eightIsSquareModThirteen ≡ false

    legendreTwentyOneOverThirteen :
      String

    legendreTwentyOneOverThirteenIsMinusOne :
      legendreTwentyOneOverThirteen ≡ "(21/13)=-1"

    qsqrtTwentyOneStatus :
      QuadraticPrimeStatus

    qsqrtTwentyOneStatusIsInert :
      qsqrtTwentyOneStatus ≡ inert

    mixedSplitInertStatusRecorded :
      Bool

    mixedSplitInertStatusRecordedIsTrue :
      mixedSplitInertStatusRecorded ≡ true

    cmSpecialCorrectionAttempted :
      Bool

    cmSpecialCorrectionAttemptedIsTrue :
      cmSpecialCorrectionAttempted ≡ true

    cmSpecialCorrectionDiagnostic :
      Bool

    cmSpecialCorrectionDiagnosticIsTrue :
      cmSpecialCorrectionDiagnostic ≡ true

    cmCorrectionCountDerived :
      Bool

    cmCorrectionCountDerivedIsFalse :
      cmCorrectionCountDerived ≡ false

    residualClosed :
      Bool

    residualClosedIsFalse :
      residualClosed ≡ false

    exactCKMPromoted :
      Bool

    exactCKMPromotedIsFalse :
      exactCKMPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalClosurePromoted :
      Bool

    terminalClosurePromotedIsFalse :
      terminalClosurePromoted ≡ false

    blockers :
      List CMCorrectionToT13Blocker

    blockersAreCanonical :
      blockers ≡ canonicalCMCorrectionToT13Blockers

    promotionFlags :
      List CMCorrectionToT13Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CMCorrectionToT13Receipt public

canonicalCMCorrectionToT13Receipt :
  CMCorrectionToT13Receipt
canonicalCMCorrectionToT13Receipt =
  record
    { status =
        t13CMSplittingArithmeticRecorded
    ; t13BaseReceipt =
        T13.canonicalDeg23FromT13HeckeReceipt
    ; t13BaseReceiptCanonical =
        true
    ; t13BaseReceiptCanonicalIsTrue =
        refl
    ; prime =
        13
    ; primeIsThirteen =
        refl
    ; minusThreeResidue =
        10
    ; minusThreeResidueIsTen =
        refl
    ; tenIsSquareModThirteen =
        true
    ; tenIsSquareModThirteenIsTrue =
        refl
    ; legendreMinusThreeOverThirteen =
        "(-3/13)=+1"
    ; legendreMinusThreeOverThirteenIsPlusOne =
        refl
    ; qsqrtMinusThreeStatus =
        split
    ; qsqrtMinusThreeStatusIsSplit =
        refl
    ; minusSevenResidue =
        6
    ; minusSevenResidueIsSix =
        refl
    ; sixIsSquareModThirteen =
        false
    ; sixIsSquareModThirteenIsFalse =
        refl
    ; legendreMinusSevenOverThirteen =
        "(-7/13)=-1"
    ; legendreMinusSevenOverThirteenIsMinusOne =
        refl
    ; qsqrtMinusSevenStatus =
        inert
    ; qsqrtMinusSevenStatusIsInert =
        refl
    ; twentyOneResidue =
        8
    ; twentyOneResidueIsEight =
        refl
    ; eightIsSquareModThirteen =
        false
    ; eightIsSquareModThirteenIsFalse =
        refl
    ; legendreTwentyOneOverThirteen =
        "(21/13)=-1"
    ; legendreTwentyOneOverThirteenIsMinusOne =
        refl
    ; qsqrtTwentyOneStatus =
        inert
    ; qsqrtTwentyOneStatusIsInert =
        refl
    ; mixedSplitInertStatusRecorded =
        true
    ; mixedSplitInertStatusRecordedIsTrue =
        refl
    ; cmSpecialCorrectionAttempted =
        true
    ; cmSpecialCorrectionAttemptedIsTrue =
        refl
    ; cmSpecialCorrectionDiagnostic =
        true
    ; cmSpecialCorrectionDiagnosticIsTrue =
        refl
    ; cmCorrectionCountDerived =
        false
    ; cmCorrectionCountDerivedIsFalse =
        refl
    ; residualClosed =
        false
    ; residualClosedIsFalse =
        refl
    ; exactCKMPromoted =
        false
    ; exactCKMPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; standardModelPromoted =
        false
    ; standardModelPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalClosurePromoted =
        false
    ; terminalClosurePromotedIsFalse =
        refl
    ; blockers =
        canonicalCMCorrectionToT13Blockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "At p=13 the D=-3 field is split while the D=-7 field is inert"
        ∷ "The real subfield Q(sqrt(21)) is inert at 13, matching the T13 base-degree receipt"
        ∷ "The CM-special correction is attempted only as a diagnostic"
        ∷ "The corrected CM-specialised Hecke count is not derived here and the residual is not closed"
        ∷ "Exact CKM, physical CKM, Standard Model, Clay, and terminal flags are all false"
        ∷ []
    }

minusThreeSplitsAtThirteen :
  qsqrtMinusThreeStatus canonicalCMCorrectionToT13Receipt ≡ split
minusThreeSplitsAtThirteen =
  refl

minusSevenInertAtThirteen :
  qsqrtMinusSevenStatus canonicalCMCorrectionToT13Receipt ≡ inert
minusSevenInertAtThirteen =
  refl

cmCorrectionToT13NotPromoted :
  physicalCKMPromoted canonicalCMCorrectionToT13Receipt ≡ false
cmCorrectionToT13NotPromoted =
  refl

cmCorrectionToT13DiagnosticAttemptRecorded :
  cmSpecialCorrectionAttempted canonicalCMCorrectionToT13Receipt ≡ true
cmCorrectionToT13DiagnosticAttemptRecorded =
  refl

cmCorrectionToT13ResidualNotClosed :
  residualClosed canonicalCMCorrectionToT13Receipt ≡ false
cmCorrectionToT13ResidualNotClosed =
  refl

cmCorrectionToT13ExactCKMFalse :
  exactCKMPromoted canonicalCMCorrectionToT13Receipt ≡ false
cmCorrectionToT13ExactCKMFalse =
  refl

cmCorrectionToT13StandardModelFalse :
  standardModelPromoted canonicalCMCorrectionToT13Receipt ≡ false
cmCorrectionToT13StandardModelFalse =
  refl

cmCorrectionToT13ClayFalse :
  clayPromoted canonicalCMCorrectionToT13Receipt ≡ false
cmCorrectionToT13ClayFalse =
  refl

cmCorrectionToT13TerminalFalse :
  terminalClosurePromoted canonicalCMCorrectionToT13Receipt ≡ false
cmCorrectionToT13TerminalFalse =
  refl
