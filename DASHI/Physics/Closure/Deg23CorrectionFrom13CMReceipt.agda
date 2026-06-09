module DASHI.Physics.Closure.Deg23CorrectionFrom13CMReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt as Deg23
import DASHI.Physics.Closure.Deg23FromT13HeckeReceipt as T13
import DASHI.Physics.Closure.ThirteenInertInBiquadraticReceipt as P13

------------------------------------------------------------------------
-- Deg23 correction attempt from the p=13 CM/biquadratic diagnostic.
--
-- The residual target is the 14 -> 14.302 gap, about 2.1 percent.  This
-- receipt records that simple p=13 norm-scale candidates, including 1/13 and
-- alpha1/13-sized labels, do not match that residual.  It is intentionally a
-- negative diagnostic receipt: the p=13 splitting data is recorded, but no
-- correction theorem or physical promotion is produced.

data Deg23CorrectionFrom13CMStatus : Set where
  prime13CMNormCandidatesDoNotCloseDeg23Residual :
    Deg23CorrectionFrom13CMStatus

data Deg23CorrectionCandidate : Set where
  candidateOneOverThirteen :
    Deg23CorrectionCandidate

  candidateTwoOverThirteen :
    Deg23CorrectionCandidate

  candidateAlphaOneOverThirteen :
    Deg23CorrectionCandidate

  candidateAlphaOneHalfOverThirteen :
    Deg23CorrectionCandidate

  candidateResidueDegreeOverThirteen :
    Deg23CorrectionCandidate

canonicalDeg23CorrectionCandidates :
  List Deg23CorrectionCandidate
canonicalDeg23CorrectionCandidates =
  candidateOneOverThirteen
  ∷ candidateTwoOverThirteen
  ∷ candidateAlphaOneOverThirteen
  ∷ candidateAlphaOneHalfOverThirteen
  ∷ candidateResidueDegreeOverThirteen
  ∷ []

data Deg23CorrectionFrom13CMBlocker : Set where
  oneOverThirteenTooLarge :
    Deg23CorrectionFrom13CMBlocker

  alphaOneOverThirteenTooSmall :
    Deg23CorrectionFrom13CMBlocker

  noNormCorrectionLaw :
    Deg23CorrectionFrom13CMBlocker

  splittingDiagnosticDoesNotSupplyResidual :
    Deg23CorrectionFrom13CMBlocker

canonicalDeg23CorrectionFrom13CMBlockers :
  List Deg23CorrectionFrom13CMBlocker
canonicalDeg23CorrectionFrom13CMBlockers =
  oneOverThirteenTooLarge
  ∷ alphaOneOverThirteenTooSmall
  ∷ noNormCorrectionLaw
  ∷ splittingDiagnosticDoesNotSupplyResidual
  ∷ []

data Deg23CorrectionFrom13CMPromotion : Set where

deg23CorrectionFrom13CMPromotionImpossibleHere :
  Deg23CorrectionFrom13CMPromotion →
  ⊥
deg23CorrectionFrom13CMPromotionImpossibleHere ()

deg23ResidualTargetLabel : String
deg23ResidualTargetLabel =
  "target deg23 residual is 302 milli-units on base 14000 milli-units, about 2.1 percent"

prime13CandidateTableLabel : String
prime13CandidateTableLabel =
  "simple candidates checked: 1/13, 2/13, alpha1/13, alpha1/(2*13), residue-degree/13"

record Deg23CorrectionFrom13CMReceipt : Setω where
  field
    status :
      Deg23CorrectionFrom13CMStatus

    residualReceipt :
      Deg23.Deg23ResidualDiagnosticReceipt

    residualReceiptIsCanonical :
      residualReceipt ≡ Deg23.canonicalDeg23ResidualDiagnosticReceipt

    t13BaseReceiptConsumed :
      Bool

    t13BaseReceiptConsumedIsTrue :
      t13BaseReceiptConsumed ≡ true

    t13BaseDegreeWitness :
      T13.t13Degree
        T13.canonicalDeg23FromT13HeckeReceipt
      ≡
      14

    prime13SplittingReceiptConsumed :
      Bool

    prime13SplittingReceiptConsumedIsTrue :
      prime13SplittingReceiptConsumed ≡ true

    prime13SplitsAsTwoDegreeTwoWitness :
      P13.twoDegreeTwoPrimeFactors
        P13.canonicalThirteenInertInBiquadraticReceipt
      ≡
      true

    residualTargetMilli :
      Nat

    residualTargetMilliIs302 :
      residualTargetMilli ≡ 302

    residualTargetBasisPoints :
      Nat

    residualTargetBasisPointsIs211 :
      residualTargetBasisPoints ≡ 211

    residualTargetStatement :
      String

    residualTargetStatementIsCanonical :
      residualTargetStatement ≡ deg23ResidualTargetLabel

    candidateTableStatement :
      String

    candidateTableStatementIsCanonical :
      candidateTableStatement ≡ prime13CandidateTableLabel

    oneOverThirteenMilli :
      Nat

    oneOverThirteenMilliIs77 :
      oneOverThirteenMilli ≡ 77

    twoOverThirteenMilli :
      Nat

    twoOverThirteenMilliIs154 :
      twoOverThirteenMilli ≡ 154

    alphaOneMilli :
      Nat

    alphaOneMilliIs41 :
      alphaOneMilli ≡ 41

    alphaOneOverThirteenMilli :
      Nat

    alphaOneOverThirteenMilliIs3 :
      alphaOneOverThirteenMilli ≡ 3

    alphaOneHalfOverThirteenMilli :
      Nat

    alphaOneHalfOverThirteenMilliIs2 :
      alphaOneHalfOverThirteenMilli ≡ 2

    closestSimpleCandidateLabel :
      String

    closestSimpleCandidateValueMilli :
      Nat

    closestSimpleCandidateValueMilliIs154 :
      closestSimpleCandidateValueMilli ≡ 154

    closestSimpleCandidateMatchesResidual :
      Bool

    closestSimpleCandidateMatchesResidualIsFalse :
      closestSimpleCandidateMatchesResidual ≡ false

    simpleNormCandidatesMatchResidual :
      Bool

    simpleNormCandidatesMatchResidualIsFalse :
      simpleNormCandidatesMatchResidual ≡ false

    correctionFromPrime13CMConstructed :
      Bool

    correctionFromPrime13CMConstructedIsFalse :
      correctionFromPrime13CMConstructed ≡ false

    candidateLabels :
      List Deg23CorrectionCandidate

    candidateLabelsAreCanonical :
      candidateLabels ≡ canonicalDeg23CorrectionCandidates

    blockers :
      List Deg23CorrectionFrom13CMBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23CorrectionFrom13CMBlockers

    promotionFlags :
      List Deg23CorrectionFrom13CMPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23CorrectionFrom13CMReceipt public

canonicalDeg23CorrectionFrom13CMReceipt :
  Deg23CorrectionFrom13CMReceipt
canonicalDeg23CorrectionFrom13CMReceipt =
  record
    { status =
        prime13CMNormCandidatesDoNotCloseDeg23Residual
    ; residualReceipt =
        Deg23.canonicalDeg23ResidualDiagnosticReceipt
    ; residualReceiptIsCanonical =
        refl
    ; t13BaseReceiptConsumed =
        true
    ; t13BaseReceiptConsumedIsTrue =
        refl
    ; t13BaseDegreeWitness =
        refl
    ; prime13SplittingReceiptConsumed =
        true
    ; prime13SplittingReceiptConsumedIsTrue =
        refl
    ; prime13SplitsAsTwoDegreeTwoWitness =
        refl
    ; residualTargetMilli =
        302
    ; residualTargetMilliIs302 =
        refl
    ; residualTargetBasisPoints =
        211
    ; residualTargetBasisPointsIs211 =
        refl
    ; residualTargetStatement =
        deg23ResidualTargetLabel
    ; residualTargetStatementIsCanonical =
        refl
    ; candidateTableStatement =
        prime13CandidateTableLabel
    ; candidateTableStatementIsCanonical =
        refl
    ; oneOverThirteenMilli =
        77
    ; oneOverThirteenMilliIs77 =
        refl
    ; twoOverThirteenMilli =
        154
    ; twoOverThirteenMilliIs154 =
        refl
    ; alphaOneMilli =
        41
    ; alphaOneMilliIs41 =
        refl
    ; alphaOneOverThirteenMilli =
        3
    ; alphaOneOverThirteenMilliIs3 =
        refl
    ; alphaOneHalfOverThirteenMilli =
        2
    ; alphaOneHalfOverThirteenMilliIs2 =
        refl
    ; closestSimpleCandidateLabel =
        "2/13 from the residue-degree-two pattern is still only about 154 milli, not 302 milli"
    ; closestSimpleCandidateValueMilli =
        154
    ; closestSimpleCandidateValueMilliIs154 =
        refl
    ; closestSimpleCandidateMatchesResidual =
        false
    ; closestSimpleCandidateMatchesResidualIsFalse =
        refl
    ; simpleNormCandidatesMatchResidual =
        false
    ; simpleNormCandidatesMatchResidualIsFalse =
        refl
    ; correctionFromPrime13CMConstructed =
        false
    ; correctionFromPrime13CMConstructedIsFalse =
        refl
    ; candidateLabels =
        canonicalDeg23CorrectionCandidates
    ; candidateLabelsAreCanonical =
        refl
    ; blockers =
        canonicalDeg23CorrectionFrom13CMBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The p=13 biquadratic splitting diagnostic is consumed only as character data"
        ∷ "Simple norm-scale candidates do not match the 302 milli-unit deg23 residual"
        ∷ "The nearest simple listed milli candidate, 2/13 ~= 154 milli, is still not the target"
        ∷ "No CM correction law or physical CKM promotion is asserted"
        ∷ []
    }

deg23CorrectionFrom13CMDoesNotCloseResidual :
  simpleNormCandidatesMatchResidual canonicalDeg23CorrectionFrom13CMReceipt
  ≡
  false
deg23CorrectionFrom13CMDoesNotCloseResidual =
  refl

deg23CorrectionFrom13CMNotConstructed :
  correctionFromPrime13CMConstructed canonicalDeg23CorrectionFrom13CMReceipt
  ≡
  false
deg23CorrectionFrom13CMNotConstructed =
  refl
