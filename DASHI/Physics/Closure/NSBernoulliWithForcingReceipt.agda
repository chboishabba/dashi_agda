module DASHI.Physics.Closure.NSBernoulliWithForcingReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes Bernoulli receipt with bounded forcing.
--
-- This receipt records the bounded-forcing correction to the high-band
-- Bernoulli argument:
--
--   d/dt e_j <= -nu p^{2j} e_j
--               + C0 p^{j+11/8} e_{j-1}^{1/2} e_j^{1/2}
--               + F_j.
--
-- Substituting w_j = e_j^{1/2} gives
--
--   w_j' <= -(1/2)nu p^{2j} w_j
--           + (C0/2) p^{j+11/8} e_{j-1}^{1/2}
--           + F_j/(2w_j).
--
-- For large w_j this yields the asymptotic bound
--
--   w_j(infty) <= C0 p^{j+11/8} e_{j-1}^{1/2}/(nu p^{2j})
--                 + sqrt(F_j/(nu p^{2j})).
--
-- Squaring with the standard two-term relaxation records
--
--   e_j <= 2e_j(0)
--          + 2 C0^2 p^{11/4}/(nu^2 p^{2j}) e_{j-1}
--          + 2F_j/(nu p^{2j}).
--
-- The forcing correction decays as p^{-2j} for bounded F_j.  This is an
-- analytic receipt only and carries no Clay/global promotion.

data NSBernoulliWithForcingStatus : Set where
  boundedForcingEnergyInequalityRecorded :
    NSBernoulliWithForcingStatus

  squareRootSubstitutionRecorded :
    NSBernoulliWithForcingStatus

  largeWjAsymptoticBoundRecorded :
    NSBernoulliWithForcingStatus

  squaredEstimateWithForcingRecorded :
    NSBernoulliWithForcingStatus

  forcingCorrectionDecayRecorded :
    NSBernoulliWithForcingStatus

  noClayOrGlobalPromotionStatus :
    NSBernoulliWithForcingStatus

canonicalNSBernoulliWithForcingStatus :
  List NSBernoulliWithForcingStatus
canonicalNSBernoulliWithForcingStatus =
  boundedForcingEnergyInequalityRecorded
  ∷ squareRootSubstitutionRecorded
  ∷ largeWjAsymptoticBoundRecorded
  ∷ squaredEstimateWithForcingRecorded
  ∷ forcingCorrectionDecayRecorded
  ∷ noClayOrGlobalPromotionStatus
  ∷ []

data BernoulliForcingEnergyInequality : Set where
  boundedForcingEnergyInequality :
    BernoulliForcingEnergyInequality

data BernoulliForcingSubstitution : Set where
  wjEqualsSqrtEj :
    BernoulliForcingSubstitution

data BernoulliForcingAsymptoticBound : Set where
  largeWjBoundWithSqrtForcing :
    BernoulliForcingAsymptoticBound

data BernoulliForcingSquaredBound : Set where
  twoE0PlusPredecessorPlusForcing :
    BernoulliForcingSquaredBound

data BernoulliForcingDecay : Set where
  forcingCorrectionDecaysLikePToMinusTwoJ :
    BernoulliForcingDecay

data NSBernoulliWithForcingPromotion : Set where

nsBernoulliWithForcingPromotionImpossibleHere :
  NSBernoulliWithForcingPromotion →
  ⊥
nsBernoulliWithForcingPromotionImpossibleHere ()

boundedForcingEnergyInequalityFormula :
  String
boundedForcingEnergyInequalityFormula =
  "d/dt e_j <= -nu p^{2j} e_j + C0 p^{j+11/8} e_{j-1}^{1/2} e_j^{1/2} + F_j"

forcingSubstitutionFormula :
  String
forcingSubstitutionFormula =
  "w_j = e_j^{1/2}"

forcingLinearizedInequalityFormula :
  String
forcingLinearizedInequalityFormula =
  "w_j' <= -(1/2)nu p^{2j} w_j + (C0/2) p^{j+11/8} e_{j-1}^{1/2} + F_j/(2w_j)"

largeWjAsymptoticBoundFormula :
  String
largeWjAsymptoticBoundFormula =
  "w_j(infty) <= C0 p^{j+11/8} e_{j-1}^{1/2}/(nu p^{2j}) + sqrt(F_j/(nu p^{2j}))"

squaredForcingBoundFormula :
  String
squaredForcingBoundFormula =
  "e_j <= 2e_j(0)+2 C0^2 p^{11/4}/(nu^2 p^{2j}) e_{j-1}+2F_j/(nu p^{2j})"

forcingCorrectionDecayFormula :
  String
forcingCorrectionDecayFormula =
  "For bounded F_j, the correction 2F_j/(nu p^{2j}) decays like p^{-2j}."

nsBernoulliWithForcingStatement :
  String
nsBernoulliWithForcingStatement =
  "Bounded-forcing Bernoulli receipt: d/dt e_j <= -nu p^{2j}e_j + C0 p^{j+11/8}e_{j-1}^{1/2}e_j^{1/2}+F_j.  With w_j=e_j^{1/2}, w_j' <= -(1/2)nu p^{2j}w_j + (C0/2)p^{j+11/8}e_{j-1}^{1/2}+F_j/(2w_j).  For large w_j, w_j(infty) <= C0 p^{j+11/8}e_{j-1}^{1/2}/(nu p^{2j}) + sqrt(F_j/(nu p^{2j})); hence e_j <= 2e_j(0)+2 C0^2 p^{11/4}/(nu^2 p^{2j})e_{j-1}+2F_j/(nu p^{2j}).  The forcing correction decays.  No Clay/global promotion is made."

record NSBernoulliWithForcingReceipt : Setω where
  field
    status :
      List NSBernoulliWithForcingStatus

    statusIsCanonical :
      status ≡ canonicalNSBernoulliWithForcingStatus

    energyInequality :
      BernoulliForcingEnergyInequality

    energyInequalityIsBoundedForcing :
      energyInequality ≡ boundedForcingEnergyInequality

    energyInequalityFormulaLabel :
      String

    energyInequalityFormulaLabelIsCanonical :
      energyInequalityFormulaLabel ≡ boundedForcingEnergyInequalityFormula

    substitution :
      BernoulliForcingSubstitution

    substitutionIsWjEqualsSqrtEj :
      substitution ≡ wjEqualsSqrtEj

    substitutionFormulaLabel :
      String

    substitutionFormulaLabelIsCanonical :
      substitutionFormulaLabel ≡ forcingSubstitutionFormula

    linearizedInequalityFormulaLabel :
      String

    linearizedInequalityFormulaLabelIsCanonical :
      linearizedInequalityFormulaLabel ≡ forcingLinearizedInequalityFormula

    largeWjRegimeRecorded :
      Bool

    largeWjRegimeRecordedIsTrue :
      largeWjRegimeRecorded ≡ true

    asymptoticBound :
      BernoulliForcingAsymptoticBound

    asymptoticBoundIsCanonical :
      asymptoticBound ≡ largeWjBoundWithSqrtForcing

    asymptoticBoundFormulaLabel :
      String

    asymptoticBoundFormulaLabelIsCanonical :
      asymptoticBoundFormulaLabel ≡ largeWjAsymptoticBoundFormula

    squaredBound :
      BernoulliForcingSquaredBound

    squaredBoundIsCanonical :
      squaredBound ≡ twoE0PlusPredecessorPlusForcing

    squaredBoundFormulaLabel :
      String

    squaredBoundFormulaLabelIsCanonical :
      squaredBoundFormulaLabel ≡ squaredForcingBoundFormula

    predecessorCoefficientExponentNumerator :
      Nat

    predecessorCoefficientExponentNumeratorIs11 :
      predecessorCoefficientExponentNumerator ≡ 11

    predecessorCoefficientExponentDenominator :
      Nat

    predecessorCoefficientExponentDenominatorIs4 :
      predecessorCoefficientExponentDenominator ≡ 4

    forcingDenominatorExponentNumerator :
      Nat

    forcingDenominatorExponentNumeratorIs2 :
      forcingDenominatorExponentNumerator ≡ 2

    forcingDenominatorExponentDenominator :
      Nat

    forcingDenominatorExponentDenominatorIs1 :
      forcingDenominatorExponentDenominator ≡ 1

    forcingCorrectionDecay :
      BernoulliForcingDecay

    forcingCorrectionDecayIsCanonical :
      forcingCorrectionDecay ≡ forcingCorrectionDecaysLikePToMinusTwoJ

    forcingCorrectionDecayFormulaLabel :
      String

    forcingCorrectionDecayFormulaLabelIsCanonical :
      forcingCorrectionDecayFormulaLabel ≡ forcingCorrectionDecayFormula

    boundedForcingAssumptionRecorded :
      Bool

    boundedForcingAssumptionRecordedIsTrue :
      boundedForcingAssumptionRecorded ≡ true

    forcingCorrectionDecays :
      Bool

    forcingCorrectionDecaysIsTrue :
      forcingCorrectionDecays ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBernoulliWithForcingStatement

    promotionFlags :
      List NSBernoulliWithForcingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSBernoulliWithForcingReceipt public

canonicalNSBernoulliWithForcingReceipt :
  NSBernoulliWithForcingReceipt
canonicalNSBernoulliWithForcingReceipt =
  record
    { status =
        canonicalNSBernoulliWithForcingStatus
    ; statusIsCanonical =
        refl
    ; energyInequality =
        boundedForcingEnergyInequality
    ; energyInequalityIsBoundedForcing =
        refl
    ; energyInequalityFormulaLabel =
        boundedForcingEnergyInequalityFormula
    ; energyInequalityFormulaLabelIsCanonical =
        refl
    ; substitution =
        wjEqualsSqrtEj
    ; substitutionIsWjEqualsSqrtEj =
        refl
    ; substitutionFormulaLabel =
        forcingSubstitutionFormula
    ; substitutionFormulaLabelIsCanonical =
        refl
    ; linearizedInequalityFormulaLabel =
        forcingLinearizedInequalityFormula
    ; linearizedInequalityFormulaLabelIsCanonical =
        refl
    ; largeWjRegimeRecorded =
        true
    ; largeWjRegimeRecordedIsTrue =
        refl
    ; asymptoticBound =
        largeWjBoundWithSqrtForcing
    ; asymptoticBoundIsCanonical =
        refl
    ; asymptoticBoundFormulaLabel =
        largeWjAsymptoticBoundFormula
    ; asymptoticBoundFormulaLabelIsCanonical =
        refl
    ; squaredBound =
        twoE0PlusPredecessorPlusForcing
    ; squaredBoundIsCanonical =
        refl
    ; squaredBoundFormulaLabel =
        squaredForcingBoundFormula
    ; squaredBoundFormulaLabelIsCanonical =
        refl
    ; predecessorCoefficientExponentNumerator =
        11
    ; predecessorCoefficientExponentNumeratorIs11 =
        refl
    ; predecessorCoefficientExponentDenominator =
        4
    ; predecessorCoefficientExponentDenominatorIs4 =
        refl
    ; forcingDenominatorExponentNumerator =
        2
    ; forcingDenominatorExponentNumeratorIs2 =
        refl
    ; forcingDenominatorExponentDenominator =
        1
    ; forcingDenominatorExponentDenominatorIs1 =
        refl
    ; forcingCorrectionDecay =
        forcingCorrectionDecaysLikePToMinusTwoJ
    ; forcingCorrectionDecayIsCanonical =
        refl
    ; forcingCorrectionDecayFormulaLabel =
        forcingCorrectionDecayFormula
    ; forcingCorrectionDecayFormulaLabelIsCanonical =
        refl
    ; boundedForcingAssumptionRecorded =
        true
    ; boundedForcingAssumptionRecordedIsTrue =
        refl
    ; forcingCorrectionDecays =
        true
    ; forcingCorrectionDecaysIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        nsBernoulliWithForcingStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records bounded-forcing Bernoulli energy inequality"
        ∷ "Records substitution w_j=e_j^{1/2}"
        ∷ "Records forced w_j inequality with F_j/(2w_j)"
        ∷ "Records large-w_j asymptotic bound with sqrt(F_j/(nu p^{2j}))"
        ∷ "Records squared bound e_j <= 2e_j(0)+2 C0^2 p^{11/4}/(nu^2 p^{2j})e_{j-1}+2F_j/(nu p^{2j})"
        ∷ "Records forcing correction decay for bounded F_j"
        ∷ "No Clay Navier-Stokes, global regularity, or terminal theorem promotion is claimed"
        ∷ []
    }

canonicalBoundedForcingEnergyInequality :
  energyInequality canonicalNSBernoulliWithForcingReceipt
  ≡
  boundedForcingEnergyInequality
canonicalBoundedForcingEnergyInequality =
  refl

canonicalForcingSubstitution :
  substitution canonicalNSBernoulliWithForcingReceipt
  ≡
  wjEqualsSqrtEj
canonicalForcingSubstitution =
  refl

canonicalSquaredBoundIncludesForcingCorrection :
  squaredBound canonicalNSBernoulliWithForcingReceipt
  ≡
  twoE0PlusPredecessorPlusForcing
canonicalSquaredBoundIncludesForcingCorrection =
  refl

canonicalForcingCorrectionDecays :
  forcingCorrectionDecays canonicalNSBernoulliWithForcingReceipt
  ≡
  true
canonicalForcingCorrectionDecays =
  refl

canonicalNSBernoulliWithForcingNoClayPromotion :
  clayNavierStokesPromoted canonicalNSBernoulliWithForcingReceipt
  ≡
  false
canonicalNSBernoulliWithForcingNoClayPromotion =
  refl

canonicalNSBernoulliWithForcingNoGlobalPromotion :
  globalRegularityPromoted canonicalNSBernoulliWithForcingReceipt
  ≡
  false
canonicalNSBernoulliWithForcingNoGlobalPromotion =
  refl

nsBernoulliWithForcingNoPromotion :
  NSBernoulliWithForcingPromotion →
  ⊥
nsBernoulliWithForcingNoPromotion =
  nsBernoulliWithForcingPromotionImpossibleHere
