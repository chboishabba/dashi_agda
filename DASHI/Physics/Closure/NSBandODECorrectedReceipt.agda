module DASHI.Physics.Closure.NSBandODECorrectedReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Corrected Navier-Stokes individual band ODE receipt.
--
-- This receipt records the corrected weighted individual-band inequality:
--
--   e_j = p^(11j/4) a_j
--
-- satisfies
--
--   d/dt e_j <= -nu p^(2j)e_j
--              + C0 p^(j+11/8)e_(j-1)^(1/2)e_j^(1/2)
--              + F_j.
--
-- The universal constant C0 is the Littlewood-Paley/Bernstein constant,
-- independent of j by scale invariance.  The exponent j + 11/8 comes from
-- one gradient factor p^j and the H^(11/8) weight p^(11/8).  The corrected
-- dissipation cutoff therefore has offset 11/8 in j_nu bookkeeping.  F_j is
-- recorded as cross-lane forcing.  This is a corrected local ODE receipt
-- only: no Clay Navier-Stokes or global regularity promotion is made.

data NSBandODECorrectedStatus : Set where
  weightedEnergyDefinitionRecorded :
    NSBandODECorrectedStatus

  correctedIndividualBandODERecorded :
    NSBandODECorrectedStatus

  universalLPBernsteinConstantRecorded :
    NSBandODECorrectedStatus

  scaleInvarianceIndependenceOfJRecorded :
    NSBandODECorrectedStatus

  crossLaneForcingTermRecorded :
    NSBandODECorrectedStatus

  exponentOriginGradientPlusH118WeightRecorded :
    NSBandODECorrectedStatus

  correctedJNuOffsetElevenEighthsRecorded :
    NSBandODECorrectedStatus

  noClayOrGlobalPromotionStatus :
    NSBandODECorrectedStatus

canonicalNSBandODECorrectedStatus :
  List NSBandODECorrectedStatus
canonicalNSBandODECorrectedStatus =
  weightedEnergyDefinitionRecorded
  ∷ correctedIndividualBandODERecorded
  ∷ universalLPBernsteinConstantRecorded
  ∷ scaleInvarianceIndependenceOfJRecorded
  ∷ crossLaneForcingTermRecorded
  ∷ exponentOriginGradientPlusH118WeightRecorded
  ∷ correctedJNuOffsetElevenEighthsRecorded
  ∷ noClayOrGlobalPromotionStatus
  ∷ []

data WeightedBandEnergy : Set where
  pToElevenJOverFourTimesAJ :
    WeightedBandEnergy

data CorrectedIndividualBandODE : Set where
  h118WeightedAdjacentODEWithCrossLaneForcing :
    CorrectedIndividualBandODE

data UniversalLPBernsteinConstant : Set where
  C0UniversalIndependentOfJ :
    UniversalLPBernsteinConstant

data ExponentOrigin : Set where
  gradientPJPlusH118WeightPElevenEighths :
    ExponentOrigin

data CrossLaneForcing : Set where
  FjCrossLaneForcing :
    CrossLaneForcing

data CorrectedJNuOffset : Set where
  elevenEighthsOffset :
    CorrectedJNuOffset

data NSBandODECorrectedPromotion : Set where

nsBandODECorrectedPromotionImpossibleHere :
  NSBandODECorrectedPromotion →
  ⊥
nsBandODECorrectedPromotionImpossibleHere ()

weightedBandEnergyFormula : String
weightedBandEnergyFormula =
  "e_j = p^(11j/4) a_j"

correctedIndividualBandODEFormula : String
correctedIndividualBandODEFormula =
  "d/dt e_j <= -nu p^(2j)e_j + C0 p^(j+11/8)e_(j-1)^(1/2)e_j^(1/2) + F_j"

universalLPBernsteinConstantFormula : String
universalLPBernsteinConstantFormula =
  "C0 is a universal LP-Bernstein constant independent of j by scale invariance"

crossLaneForcingFormula : String
crossLaneForcingFormula =
  "F_j is the cross-lane forcing term"

exponentOriginFormula : String
exponentOriginFormula =
  "p^(j+11/8) = gradient p^j times H^(11/8) weight p^(11/8)"

correctedJNuOffsetFormula : String
correctedJNuOffsetFormula =
  "j_nu cutoff bookkeeping uses corrected offset 11/8"

nsBandODECorrectedStatement : String
nsBandODECorrectedStatement =
  "Corrected individual NS band ODE: weighted energy e_j=p^(11j/4)a_j satisfies d/dt e_j <= -nu p^(2j)e_j + C0 p^(j+11/8)e_(j-1)^(1/2)e_j^(1/2) + F_j; C0 is the universal LP-Bernstein constant independent of j by scale invariance; F_j is cross-lane forcing; exponent j+11/8 comes from gradient p^j plus H^(11/8) weight p^(11/8); the corrected j_nu offset is 11/8. No Clay or global promotion follows."

record NSBandODECorrectedReceipt : Setω where
  field
    status :
      List NSBandODECorrectedStatus

    statusIsCanonical :
      status ≡ canonicalNSBandODECorrectedStatus

    weightedBandEnergy :
      WeightedBandEnergy

    weightedBandEnergyIsCanonical :
      weightedBandEnergy ≡ pToElevenJOverFourTimesAJ

    weightedBandEnergyFormulaLabel :
      String

    weightedBandEnergyFormulaLabelIsCanonical :
      weightedBandEnergyFormulaLabel ≡ weightedBandEnergyFormula

    correctedBandODE :
      CorrectedIndividualBandODE

    correctedBandODEIsCanonical :
      correctedBandODE ≡ h118WeightedAdjacentODEWithCrossLaneForcing

    correctedBandODEFormulaLabel :
      String

    correctedBandODEFormulaLabelIsCanonical :
      correctedBandODEFormulaLabel ≡ correctedIndividualBandODEFormula

    lpBernsteinConstant :
      UniversalLPBernsteinConstant

    lpBernsteinConstantIsUniversal :
      lpBernsteinConstant ≡ C0UniversalIndependentOfJ

    lpBernsteinConstantFormulaLabel :
      String

    lpBernsteinConstantFormulaLabelIsCanonical :
      lpBernsteinConstantFormulaLabel ≡ universalLPBernsteinConstantFormula

    c0IndependentOfJ :
      Bool

    c0IndependentOfJIsTrue :
      c0IndependentOfJ ≡ true

    c0IndependenceReasonScaleInvariance :
      Bool

    c0IndependenceReasonScaleInvarianceIsTrue :
      c0IndependenceReasonScaleInvariance ≡ true

    crossLaneForcing :
      CrossLaneForcing

    crossLaneForcingIsFj :
      crossLaneForcing ≡ FjCrossLaneForcing

    crossLaneForcingFormulaLabel :
      String

    crossLaneForcingFormulaLabelIsCanonical :
      crossLaneForcingFormulaLabel ≡ crossLaneForcingFormula

    crossLaneForcingRecorded :
      Bool

    crossLaneForcingRecordedIsTrue :
      crossLaneForcingRecorded ≡ true

    exponentOrigin :
      ExponentOrigin

    exponentOriginIsGradientPlusH118Weight :
      exponentOrigin ≡ gradientPJPlusH118WeightPElevenEighths

    exponentOriginFormulaLabel :
      String

    exponentOriginFormulaLabelIsCanonical :
      exponentOriginFormulaLabel ≡ exponentOriginFormula

    gradientExponentNumerator :
      Nat

    gradientExponentNumeratorIs1 :
      gradientExponentNumerator ≡ 1

    h118WeightNumerator :
      Nat

    h118WeightNumeratorIs11 :
      h118WeightNumerator ≡ 11

    h118WeightDenominator :
      Nat

    h118WeightDenominatorIs8 :
      h118WeightDenominator ≡ 8

    correctedJNuOffset :
      CorrectedJNuOffset

    correctedJNuOffsetIsElevenEighths :
      correctedJNuOffset ≡ elevenEighthsOffset

    correctedJNuOffsetFormulaLabel :
      String

    correctedJNuOffsetFormulaLabelIsCanonical :
      correctedJNuOffsetFormulaLabel ≡ correctedJNuOffsetFormula

    correctedJNuOffsetNumerator :
      Nat

    correctedJNuOffsetNumeratorIs11 :
      correctedJNuOffsetNumerator ≡ 11

    correctedJNuOffsetDenominator :
      Nat

    correctedJNuOffsetDenominatorIs8 :
      correctedJNuOffsetDenominator ≡ 8

    noClayPromotion :
      Bool

    noClayPromotionIsTrue :
      noClayPromotion ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBandODECorrectedStatement

    promotionFlags :
      List NSBandODECorrectedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSBandODECorrectedReceipt public

canonicalNSBandODECorrectedReceipt :
  NSBandODECorrectedReceipt
canonicalNSBandODECorrectedReceipt =
  record
    { status =
        canonicalNSBandODECorrectedStatus
    ; statusIsCanonical =
        refl
    ; weightedBandEnergy =
        pToElevenJOverFourTimesAJ
    ; weightedBandEnergyIsCanonical =
        refl
    ; weightedBandEnergyFormulaLabel =
        weightedBandEnergyFormula
    ; weightedBandEnergyFormulaLabelIsCanonical =
        refl
    ; correctedBandODE =
        h118WeightedAdjacentODEWithCrossLaneForcing
    ; correctedBandODEIsCanonical =
        refl
    ; correctedBandODEFormulaLabel =
        correctedIndividualBandODEFormula
    ; correctedBandODEFormulaLabelIsCanonical =
        refl
    ; lpBernsteinConstant =
        C0UniversalIndependentOfJ
    ; lpBernsteinConstantIsUniversal =
        refl
    ; lpBernsteinConstantFormulaLabel =
        universalLPBernsteinConstantFormula
    ; lpBernsteinConstantFormulaLabelIsCanonical =
        refl
    ; c0IndependentOfJ =
        true
    ; c0IndependentOfJIsTrue =
        refl
    ; c0IndependenceReasonScaleInvariance =
        true
    ; c0IndependenceReasonScaleInvarianceIsTrue =
        refl
    ; crossLaneForcing =
        FjCrossLaneForcing
    ; crossLaneForcingIsFj =
        refl
    ; crossLaneForcingFormulaLabel =
        crossLaneForcingFormula
    ; crossLaneForcingFormulaLabelIsCanonical =
        refl
    ; crossLaneForcingRecorded =
        true
    ; crossLaneForcingRecordedIsTrue =
        refl
    ; exponentOrigin =
        gradientPJPlusH118WeightPElevenEighths
    ; exponentOriginIsGradientPlusH118Weight =
        refl
    ; exponentOriginFormulaLabel =
        exponentOriginFormula
    ; exponentOriginFormulaLabelIsCanonical =
        refl
    ; gradientExponentNumerator =
        1
    ; gradientExponentNumeratorIs1 =
        refl
    ; h118WeightNumerator =
        11
    ; h118WeightNumeratorIs11 =
        refl
    ; h118WeightDenominator =
        8
    ; h118WeightDenominatorIs8 =
        refl
    ; correctedJNuOffset =
        elevenEighthsOffset
    ; correctedJNuOffsetIsElevenEighths =
        refl
    ; correctedJNuOffsetFormulaLabel =
        correctedJNuOffsetFormula
    ; correctedJNuOffsetFormulaLabelIsCanonical =
        refl
    ; correctedJNuOffsetNumerator =
        11
    ; correctedJNuOffsetNumeratorIs11 =
        refl
    ; correctedJNuOffsetDenominator =
        8
    ; correctedJNuOffsetDenominatorIs8 =
        refl
    ; noClayPromotion =
        true
    ; noClayPromotionIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; statement =
        nsBandODECorrectedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Weighted energy recorded as e_j = p^(11j/4) a_j"
        ∷ "Corrected ODE: d/dt e_j <= -nu p^(2j)e_j + C0 p^(j+11/8)e_(j-1)^(1/2)e_j^(1/2) + F_j"
        ∷ "C0 is the universal LP-Bernstein constant independent of j by scale invariance"
        ∷ "F_j records cross-lane forcing"
        ∷ "Exponent origin: gradient p^j plus H^(11/8) weight p^(11/8)"
        ∷ "Corrected j_nu offset is 11/8"
        ∷ "No Clay Navier-Stokes or global regularity promotion is made"
        ∷ []
    }

correctedBandODEFormulaIsRecorded :
  correctedBandODEFormulaLabel canonicalNSBandODECorrectedReceipt
  ≡
  correctedIndividualBandODEFormula
correctedBandODEFormulaIsRecorded =
  refl

c0UniversalAndIndependentOfJ :
  c0IndependentOfJ canonicalNSBandODECorrectedReceipt ≡ true
c0UniversalAndIndependentOfJ =
  refl

crossLaneForcingFjIsRecorded :
  crossLaneForcingRecorded canonicalNSBandODECorrectedReceipt ≡ true
crossLaneForcingFjIsRecorded =
  refl

correctedJNuOffsetIsElevenOverEight :
  correctedJNuOffsetNumerator canonicalNSBandODECorrectedReceipt ≡ 11
correctedJNuOffsetIsElevenOverEight =
  refl

nsBandODECorrectedDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSBandODECorrectedReceipt ≡ false
nsBandODECorrectedDoesNotPromoteClay =
  refl

nsBandODECorrectedDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSBandODECorrectedReceipt ≡ false
nsBandODECorrectedDoesNotPromoteGlobalRegularity =
  refl

nsBandODECorrectedNoPromotion :
  NSBandODECorrectedPromotion →
  ⊥
nsBandODECorrectedNoPromotion =
  nsBandODECorrectedPromotionImpossibleHere
