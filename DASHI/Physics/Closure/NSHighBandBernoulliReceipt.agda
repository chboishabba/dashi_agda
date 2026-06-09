module DASHI.Physics.Closure.NSHighBandBernoulliReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes high-band Bernoulli receipt.
--
-- For the first dissipative high band j = j_nu + 1, the weighted band
-- energy
--
--   e_j = p^{11j/4} a_j
--
-- is recorded as satisfying
--
--   d/dt e_j <= -nu p^{2j} e_j + C p^j e_{j-1}^{1/2} e_j^{1/2}.
--
-- With w_j = e_j^{1/2}, this becomes the linear differential inequality
--
--   w_j' <= -(1/2)nu p^{2j} w_j + (C p^j/2)e_{j-1}^{1/2}.
--
-- Bounded forcing gives
--
--   w_j(t) <= w_j(0) exp(-1/2 nu p^{2j}t)
--             + C e_{j-1}^{1/2}/(nu p^j).
--
-- The recorded induction step is upward: if the predecessor high-band
-- forcing is bounded, then the current high band is bounded; starting at
-- j_nu + 1, every band j > j_nu is covered.  This is an analytic receipt
-- only and carries no Clay/global terminal promotion.

data NSHighBandBernoulliStatus : Set where
  firstHighBandIsJNuPlusOne :
    NSHighBandBernoulliStatus

  weightedBandEnergyRecorded :
    NSHighBandBernoulliStatus

  bernoulliEnergyInequalityRecorded :
    NSHighBandBernoulliStatus

  BernoulliToLinearSubstitutionRecorded :
    NSHighBandBernoulliStatus

  boundedForcingLinearODESolutionRecorded :
    NSHighBandBernoulliStatus

  upwardHighBandInductionRecorded :
    NSHighBandBernoulliStatus

  eachHighBandAboveJNuBounded :
    NSHighBandBernoulliStatus

  noClayOrTerminalPromotionStatus :
    NSHighBandBernoulliStatus

canonicalNSHighBandBernoulliStatus :
  List NSHighBandBernoulliStatus
canonicalNSHighBandBernoulliStatus =
  firstHighBandIsJNuPlusOne
  ∷ weightedBandEnergyRecorded
  ∷ bernoulliEnergyInequalityRecorded
  ∷ BernoulliToLinearSubstitutionRecorded
  ∷ boundedForcingLinearODESolutionRecorded
  ∷ upwardHighBandInductionRecorded
  ∷ eachHighBandAboveJNuBounded
  ∷ noClayOrTerminalPromotionStatus
  ∷ []

data CriticalAlgebraicStep : Set where
  BernoulliToLinearSubstitution :
    CriticalAlgebraicStep

data HighBandPosition : Set where
  firstHighBand :
    (j-nu : Nat) →
    HighBandPosition

  successorHighBand :
    (j-nu : Nat) →
    (offset : Nat) →
    HighBandPosition

canonicalFirstHighBand :
  Nat →
  HighBandPosition
canonicalFirstHighBand j-nu =
  firstHighBand j-nu

firstHighBandIndex :
  Nat →
  Nat
firstHighBandIndex j-nu =
  suc j-nu

data WeightedBandEnergy : Set where
  pToElevenJOverFourTimesAJ :
    WeightedBandEnergy

data HighBandEnergyInequality : Set where
  bernoulliHighBandEnergyInequality :
    HighBandEnergyInequality

data LinearizedHighBandInequality : Set where
  linearWjInequality :
    LinearizedHighBandInequality

data LinearODESolutionBound : Set where
  exponentialDampingPlusBoundedForcing :
    LinearODESolutionBound

data UpwardInductionStep : Set where
  predecessorBoundedForcingBoundsCurrentHighBand :
    UpwardInductionStep

data NSHighBandBernoulliPromotion : Set where

nsHighBandBernoulliPromotionImpossibleHere :
  NSHighBandBernoulliPromotion →
  ⊥
nsHighBandBernoulliPromotionImpossibleHere ()

weightedBandEnergyFormula :
  String
weightedBandEnergyFormula =
  "e_j = p^{11j/4} a_j"

bernoulliEnergyInequalityFormula :
  String
bernoulliEnergyInequalityFormula =
  "d/dt e_j <= -nu p^{2j} e_j + C p^j e_{j-1}^{1/2} e_j^{1/2}"

linearSubstitutionFormula :
  String
linearSubstitutionFormula =
  "w_j = e_j^{1/2}"

linearizedInequalityFormula :
  String
linearizedInequalityFormula =
  "w_j' <= -(1/2)nu p^{2j} w_j + (C p^j/2)e_{j-1}^{1/2}"

solutionBoundFormula :
  String
solutionBoundFormula =
  "w_j(t) <= w_j(0) exp(-1/2 nu p^{2j}t) + C e_{j-1}^{1/2}/(nu p^j)"

upwardInductionFormula :
  String
upwardInductionFormula =
  "If e_{j-1}^{1/2} is bounded, the linear ODE bound makes w_j bounded; hence every high band j > j_nu is bounded by upward induction from j_nu+1."

nsHighBandBernoulliStatement :
  String
nsHighBandBernoulliStatement =
  "For the first high band j=j_nu+1, the weighted energy e_j=p^{11j/4}a_j obeys d/dt e_j <= -nu p^{2j}e_j + C p^j e_{j-1}^{1/2}e_j^{1/2}.  Substituting w_j=e_j^{1/2} gives w_j' <= -(1/2)nu p^{2j}w_j + (C p^j/2)e_{j-1}^{1/2}; bounded forcing yields w_j(t) <= w_j(0)exp(-1/2 nu p^{2j}t) + C e_{j-1}^{1/2}/(nu p^j).  Upward induction records each high band j>j_nu as bounded.  No Clay/global terminal promotion is made."

record NSHighBandBernoulliReceipt : Setω where
  field
    status :
      List NSHighBandBernoulliStatus

    statusIsCanonical :
      status ≡ canonicalNSHighBandBernoulliStatus

    criticalBandIndex :
      Nat

    firstHighBandIndexValue :
      Nat

    firstHighBandIndexIsJNuPlusOne :
      firstHighBandIndexValue ≡ firstHighBandIndex criticalBandIndex

    firstBandPosition :
      HighBandPosition

    firstBandPositionIsCanonical :
      firstBandPosition ≡ canonicalFirstHighBand criticalBandIndex

    highBandConditionRecorded :
      Bool

    highBandConditionRecordedIsTrue :
      highBandConditionRecorded ≡ true

    weightedBandEnergy :
      WeightedBandEnergy

    weightedBandEnergyIsCanonical :
      weightedBandEnergy ≡ pToElevenJOverFourTimesAJ

    weightedBandEnergyFormulaLabel :
      String

    weightedBandEnergyFormulaLabelIsCanonical :
      weightedBandEnergyFormulaLabel ≡ weightedBandEnergyFormula

    energyInequality :
      HighBandEnergyInequality

    energyInequalityIsBernoulli :
      energyInequality ≡ bernoulliHighBandEnergyInequality

    energyInequalityFormulaLabel :
      String

    energyInequalityFormulaLabelIsCanonical :
      energyInequalityFormulaLabel ≡ bernoulliEnergyInequalityFormula

    criticalAlgebraicStep :
      CriticalAlgebraicStep

    criticalAlgebraicStepIsBernoulliToLinearSubstitution :
      criticalAlgebraicStep ≡ BernoulliToLinearSubstitution

    substitutionFormulaLabel :
      String

    substitutionFormulaLabelIsCanonical :
      substitutionFormulaLabel ≡ linearSubstitutionFormula

    linearizedInequality :
      LinearizedHighBandInequality

    linearizedInequalityIsCanonical :
      linearizedInequality ≡ linearWjInequality

    linearizedInequalityFormulaLabel :
      String

    linearizedInequalityFormulaLabelIsCanonical :
      linearizedInequalityFormulaLabel ≡ linearizedInequalityFormula

    forcingBoundedByPredecessor :
      Bool

    forcingBoundedByPredecessorIsTrue :
      forcingBoundedByPredecessor ≡ true

    linearODESolutionBound :
      LinearODESolutionBound

    linearODESolutionBoundIsCanonical :
      linearODESolutionBound ≡ exponentialDampingPlusBoundedForcing

    solutionBoundFormulaLabel :
      String

    solutionBoundFormulaLabelIsCanonical :
      solutionBoundFormulaLabel ≡ solutionBoundFormula

    upwardInductionStep :
      UpwardInductionStep

    upwardInductionStepIsCanonical :
      upwardInductionStep
      ≡
      predecessorBoundedForcingBoundsCurrentHighBand

    upwardInductionRecorded :
      Bool

    upwardInductionRecordedIsTrue :
      upwardInductionRecorded ≡ true

    upwardInductionFormulaLabel :
      String

    upwardInductionFormulaLabelIsCanonical :
      upwardInductionFormulaLabel ≡ upwardInductionFormula

    eachHighBandGreaterThanJNuBounded :
      Bool

    eachHighBandGreaterThanJNuBoundedIsTrue :
      eachHighBandGreaterThanJNuBounded ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalTerminalPromotion :
      Bool

    globalTerminalPromotionIsFalse :
      globalTerminalPromotion ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsHighBandBernoulliStatement

    promotionFlags :
      List NSHighBandBernoulliPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSHighBandBernoulliReceipt public

canonicalNSHighBandBernoulliReceipt :
  NSHighBandBernoulliReceipt
canonicalNSHighBandBernoulliReceipt =
  record
    { status =
        canonicalNSHighBandBernoulliStatus
    ; statusIsCanonical =
        refl
    ; criticalBandIndex =
        0
    ; firstHighBandIndexValue =
        1
    ; firstHighBandIndexIsJNuPlusOne =
        refl
    ; firstBandPosition =
        canonicalFirstHighBand 0
    ; firstBandPositionIsCanonical =
        refl
    ; highBandConditionRecorded =
        true
    ; highBandConditionRecordedIsTrue =
        refl
    ; weightedBandEnergy =
        pToElevenJOverFourTimesAJ
    ; weightedBandEnergyIsCanonical =
        refl
    ; weightedBandEnergyFormulaLabel =
        weightedBandEnergyFormula
    ; weightedBandEnergyFormulaLabelIsCanonical =
        refl
    ; energyInequality =
        bernoulliHighBandEnergyInequality
    ; energyInequalityIsBernoulli =
        refl
    ; energyInequalityFormulaLabel =
        bernoulliEnergyInequalityFormula
    ; energyInequalityFormulaLabelIsCanonical =
        refl
    ; criticalAlgebraicStep =
        BernoulliToLinearSubstitution
    ; criticalAlgebraicStepIsBernoulliToLinearSubstitution =
        refl
    ; substitutionFormulaLabel =
        linearSubstitutionFormula
    ; substitutionFormulaLabelIsCanonical =
        refl
    ; linearizedInequality =
        linearWjInequality
    ; linearizedInequalityIsCanonical =
        refl
    ; linearizedInequalityFormulaLabel =
        linearizedInequalityFormula
    ; linearizedInequalityFormulaLabelIsCanonical =
        refl
    ; forcingBoundedByPredecessor =
        true
    ; forcingBoundedByPredecessorIsTrue =
        refl
    ; linearODESolutionBound =
        exponentialDampingPlusBoundedForcing
    ; linearODESolutionBoundIsCanonical =
        refl
    ; solutionBoundFormulaLabel =
        solutionBoundFormula
    ; solutionBoundFormulaLabelIsCanonical =
        refl
    ; upwardInductionStep =
        predecessorBoundedForcingBoundsCurrentHighBand
    ; upwardInductionStepIsCanonical =
        refl
    ; upwardInductionRecorded =
        true
    ; upwardInductionRecordedIsTrue =
        refl
    ; upwardInductionFormulaLabel =
        upwardInductionFormula
    ; upwardInductionFormulaLabelIsCanonical =
        refl
    ; eachHighBandGreaterThanJNuBounded =
        true
    ; eachHighBandGreaterThanJNuBoundedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalTerminalPromotion =
        false
    ; globalTerminalPromotionIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        nsHighBandBernoulliStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "First high band recorded as j=j_nu+1"
        ∷ "Weighted band energy recorded as e_j=p^{11j/4} a_j"
        ∷ "Bernoulli inequality recorded: d/dt e_j <= -nu p^{2j} e_j + C p^j e_{j-1}^{1/2} e_j^{1/2}"
        ∷ "criticalAlgebraicStep=BernoulliToLinearSubstitution with w_j=e_j^{1/2}"
        ∷ "Linear inequality recorded: w_j' <= -(1/2)nu p^{2j}w_j + (C p^j/2)e_{j-1}^{1/2}"
        ∷ "Bounded forcing solution recorded: w_j(t) <= w_j(0) exp(-1/2 nu p^{2j}t)+ C e_{j-1}^{1/2}/(nu p^j)"
        ∷ "Upward induction records each high band j>j_nu as bounded"
        ∷ "No Clay Navier-Stokes, global terminal, or terminal theorem promotion is claimed"
        ∷ []
    }

canonicalCriticalAlgebraicStepIsBernoulliToLinearSubstitution :
  criticalAlgebraicStep canonicalNSHighBandBernoulliReceipt
  ≡
  BernoulliToLinearSubstitution
canonicalCriticalAlgebraicStepIsBernoulliToLinearSubstitution =
  refl

canonicalFirstHighBandIsJNuPlusOne :
  firstHighBandIndexValue canonicalNSHighBandBernoulliReceipt
  ≡
  firstHighBandIndex (criticalBandIndex canonicalNSHighBandBernoulliReceipt)
canonicalFirstHighBandIsJNuPlusOne =
  refl

canonicalHighBandBoundedByUpwardInduction :
  eachHighBandGreaterThanJNuBounded canonicalNSHighBandBernoulliReceipt
  ≡
  true
canonicalHighBandBoundedByUpwardInduction =
  refl

canonicalNSHighBandBernoulliNoClayPromotion :
  clayNavierStokesPromoted canonicalNSHighBandBernoulliReceipt
  ≡
  false
canonicalNSHighBandBernoulliNoClayPromotion =
  refl

canonicalNSHighBandBernoulliNoGlobalTerminalPromotion :
  globalTerminalPromotion canonicalNSHighBandBernoulliReceipt
  ≡
  false
canonicalNSHighBandBernoulliNoGlobalTerminalPromotion =
  refl

canonicalNSHighBandBernoulliNoTerminalPromotion :
  terminalClaimPromoted canonicalNSHighBandBernoulliReceipt
  ≡
  false
canonicalNSHighBandBernoulliNoTerminalPromotion =
  refl

nsHighBandBernoulliNoPromotion :
  NSHighBandBernoulliPromotion →
  ⊥
nsHighBandBernoulliNoPromotion =
  nsHighBandBernoulliPromotionImpossibleHere
