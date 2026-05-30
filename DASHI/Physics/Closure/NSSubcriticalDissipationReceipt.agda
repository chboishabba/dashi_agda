module DASHI.Physics.Closure.NSSubcriticalDissipationReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes adjacent-only subcritical dissipation receipt.
--
-- This receipt records the corrected adjacent-band calculation:
-- stretching is nearest-neighbour only and is bounded by
--   |T_{p,j,j-1}| <= C p^{15j/4 - 1} a_j a_{j-1}^{1/2},
-- while the high-frequency dissipation is
--   nu p^{2j} e_j = nu p^{4j} a_j.
-- The corrected carrier threshold is s >= 11/8 for large-data dissipation
-- dominance.  Below threshold, 0 < s < 11/8, this receipt records only the
-- small-data lane.
-- No Clay Navier-Stokes or global-regularity promotion is made here.

data NSAdjacentDissipationIngredient : Set where
  adjacentOnlyStretchingEstimate :
    NSAdjacentDissipationIngredient

  highFrequencyDissipationIdentity :
    NSAdjacentDissipationIngredient

  correctedExponentDominanceCalculation :
    NSAdjacentDissipationIngredient

  thresholdSobolevIndexScope :
    NSAdjacentDissipationIngredient

canonicalNSAdjacentDissipationIngredients :
  List NSAdjacentDissipationIngredient
canonicalNSAdjacentDissipationIngredients =
  adjacentOnlyStretchingEstimate
  ∷ highFrequencyDissipationIdentity
  ∷ correctedExponentDominanceCalculation
  ∷ thresholdSobolevIndexScope
  ∷ []

data NSAdjacentDissipationStatus : Set where
  adjacentOnlyStretchingRecorded :
    NSAdjacentDissipationStatus

  dissipationIdentityStatusRecorded :
    NSAdjacentDissipationStatus

  dominanceConditionCorrected :
    NSAdjacentDissipationStatus

  highFrequencyDominanceForSGreaterEqualElevenOverEight :
    NSAdjacentDissipationStatus

  belowThresholdSmallDataOnlyStatus :
    NSAdjacentDissipationStatus

  notHSevenFourOnly :
    NSAdjacentDissipationStatus

  noClayPromotion :
    NSAdjacentDissipationStatus

canonicalNSAdjacentDissipationStatus :
  List NSAdjacentDissipationStatus
canonicalNSAdjacentDissipationStatus =
  adjacentOnlyStretchingRecorded
  ∷ dissipationIdentityStatusRecorded
  ∷ dominanceConditionCorrected
  ∷ highFrequencyDominanceForSGreaterEqualElevenOverEight
  ∷ belowThresholdSmallDataOnlyStatus
  ∷ notHSevenFourOnly
  ∷ noClayPromotion
  ∷ []

data NSAdjacentDissipationPromotion : Set where

nsAdjacentDissipationPromotionImpossibleHere :
  NSAdjacentDissipationPromotion →
  ⊥
nsAdjacentDissipationPromotionImpossibleHere ()

data NSStretchingEstimate : Set where
  adjacentOnlyTpjminusOneBound :
    NSStretchingEstimate

data NSDissipationIdentity : Set where
  highFrequencyNuP2jEjEqualsNuP4jAj :
    NSDissipationIdentity

data NSDominanceCalculation : Set where
  correctedMarginJOverFourPlusOne :
    NSDominanceCalculation

data NSSobolevScope : Set where
  thresholdAtElevenOverEight :
    NSSobolevScope

nsCarrierThresholdText :
  String
nsCarrierThresholdText =
  "11/8"

nsAdjacentOnlyDissipationStatement :
  String
nsAdjacentOnlyDissipationStatement =
  "Adjacent-only NS stretching has |T_{p,j,j-1}| <= C p^{15j/4 - 1} a_j a_{j-1}^{1/2}; dissipation is nu p^{2j} e_j = nu p^{4j} a_j; the corrected carrier threshold is s >= 11/8 for large-data dissipation dominance, while 0 < s < 11/8 is small-data only; no Clay promotion follows."

stretchingEstimateFormula :
  String
stretchingEstimateFormula =
  "|T_{p,j,j-1}| <= C p^{15j/4 - 1} a_j a_{j-1}^{1/2}"

dissipationIdentityFormula :
  String
dissipationIdentityFormula =
  "nu p^{2j} e_j = nu p^{4j} a_j"

dominanceCalculationFormula :
  String
dominanceCalculationFormula =
  "4j - (15j/4 - 1) = j/4 + 1"

record NSSubcriticalDissipationReceipt : Setω where
  field
    ingredients :
      List NSAdjacentDissipationIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalNSAdjacentDissipationIngredients

    status :
      List NSAdjacentDissipationStatus

    statusIsCanonical :
      status ≡ canonicalNSAdjacentDissipationStatus

    stretchingEstimate :
      NSStretchingEstimate

    stretchingEstimateIsAdjacentOnlyTpjminusOneBound :
      stretchingEstimate ≡ adjacentOnlyTpjminusOneBound

    stretchingFormula :
      String

    stretchingFormulaIsCanonical :
      stretchingFormula ≡ stretchingEstimateFormula

    dissipationIdentity :
      NSDissipationIdentity

    dissipationIdentityIsHighFrequencyNuP2jEjEqualsNuP4jAj :
      dissipationIdentity ≡ highFrequencyNuP2jEjEqualsNuP4jAj

    dissipationFormula :
      String

    dissipationFormulaIsCanonical :
      dissipationFormula ≡ dissipationIdentityFormula

    dominanceCalculation :
      NSDominanceCalculation

    dominanceCalculationIsCorrectedMarginJOverFourPlusOne :
      dominanceCalculation ≡ correctedMarginJOverFourPlusOne

    dominanceCalculationString :
      String

    dominanceCalculationStringIsCanonical :
      dominanceCalculationString ≡ dominanceCalculationFormula

    sobolevScope :
      NSSobolevScope

    sobolevScopeIsThresholdAtElevenOverEight :
      sobolevScope ≡ thresholdAtElevenOverEight

    adjacentOnlyStretchingEstimateRecorded :
      Bool

    adjacentOnlyStretchingEstimateRecordedIsTrue :
      adjacentOnlyStretchingEstimateRecorded ≡ true

    dissipationIdentityRecorded :
      Bool

    dissipationIdentityRecordedIsTrue :
      dissipationIdentityRecorded ≡ true

    correctedDominanceCalculationRecorded :
      Bool

    correctedDominanceCalculationRecordedIsTrue :
      correctedDominanceCalculationRecorded ≡ true

    nsCarrierThreshold :
      String

    nsCarrierThresholdIsElevenOverEight :
      nsCarrierThreshold ≡ nsCarrierThresholdText

    subcriticalDissipationForAnySPositive :
      Bool

    subcriticalDissipationForAnySPositiveIsFalse :
      subcriticalDissipationForAnySPositive ≡ false

    subcriticalDissipationForS>=11/8 :
      Bool

    subcriticalDissipationForS>=11/8IsTrue :
      subcriticalDissipationForS>=11/8 ≡ true

    belowThresholdSmallDataOnly :
      Bool

    belowThresholdSmallDataOnlyIsTrue :
      belowThresholdSmallDataOnly ≡ true

    dissipationDominatesStretchingAtHighFrequency :
      Bool

    dissipationDominatesStretchingAtHighFrequencyIsTrue :
      dissipationDominatesStretchingAtHighFrequency ≡ true

    nsAdjacentOnlyDissipationDominanceForS>=11/8 :
      Bool

    nsAdjacentOnlyDissipationDominanceForS>=11/8IsTrue :
      nsAdjacentOnlyDissipationDominanceForS>=11/8 ≡ true

    hSevenFourOnlyCondition :
      Bool

    hSevenFourOnlyConditionIsFalse :
      hSevenFourOnlyCondition ≡ false

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
      statement ≡ nsAdjacentOnlyDissipationStatement

    promotionFlags :
      List NSAdjacentDissipationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSSubcriticalDissipationReceipt public

canonicalNSSubcriticalDissipationReceipt :
  NSSubcriticalDissipationReceipt
canonicalNSSubcriticalDissipationReceipt =
  record
    { ingredients =
        canonicalNSAdjacentDissipationIngredients
    ; ingredientsAreCanonical =
        refl
    ; status =
        canonicalNSAdjacentDissipationStatus
    ; statusIsCanonical =
        refl
    ; stretchingEstimate =
        adjacentOnlyTpjminusOneBound
    ; stretchingEstimateIsAdjacentOnlyTpjminusOneBound =
        refl
    ; stretchingFormula =
        stretchingEstimateFormula
    ; stretchingFormulaIsCanonical =
        refl
    ; dissipationIdentity =
        highFrequencyNuP2jEjEqualsNuP4jAj
    ; dissipationIdentityIsHighFrequencyNuP2jEjEqualsNuP4jAj =
        refl
    ; dissipationFormula =
        dissipationIdentityFormula
    ; dissipationFormulaIsCanonical =
        refl
    ; dominanceCalculation =
        correctedMarginJOverFourPlusOne
    ; dominanceCalculationIsCorrectedMarginJOverFourPlusOne =
        refl
    ; dominanceCalculationString =
        dominanceCalculationFormula
    ; dominanceCalculationStringIsCanonical =
        refl
    ; sobolevScope =
        thresholdAtElevenOverEight
    ; sobolevScopeIsThresholdAtElevenOverEight =
        refl
    ; adjacentOnlyStretchingEstimateRecorded =
        true
    ; adjacentOnlyStretchingEstimateRecordedIsTrue =
        refl
    ; dissipationIdentityRecorded =
        true
    ; dissipationIdentityRecordedIsTrue =
        refl
    ; correctedDominanceCalculationRecorded =
        true
    ; correctedDominanceCalculationRecordedIsTrue =
        refl
    ; nsCarrierThreshold =
        nsCarrierThresholdText
    ; nsCarrierThresholdIsElevenOverEight =
        refl
    ; subcriticalDissipationForAnySPositive =
        false
    ; subcriticalDissipationForAnySPositiveIsFalse =
        refl
    ; subcriticalDissipationForS>=11/8 =
        true
    ; subcriticalDissipationForS>=11/8IsTrue =
        refl
    ; belowThresholdSmallDataOnly =
        true
    ; belowThresholdSmallDataOnlyIsTrue =
        refl
    ; dissipationDominatesStretchingAtHighFrequency =
        true
    ; dissipationDominatesStretchingAtHighFrequencyIsTrue =
        refl
    ; nsAdjacentOnlyDissipationDominanceForS>=11/8 =
        true
    ; nsAdjacentOnlyDissipationDominanceForS>=11/8IsTrue =
        refl
    ; hSevenFourOnlyCondition =
        false
    ; hSevenFourOnlyConditionIsFalse =
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
        nsAdjacentOnlyDissipationStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Stretching is recorded only for adjacent band interaction T_{p,j,j-1}"
        ∷ "Stretching estimate: |T_{p,j,j-1}| <= C p^{15j/4 - 1} a_j a_{j-1}^{1/2}"
        ∷ "High-frequency dissipation identity: nu p^{2j} e_j = nu p^{4j} a_j"
        ∷ "Corrected carrier threshold: s >= 11/8 for large-data dissipation dominance"
        ∷ "Below threshold, 0 < s < 11/8, only the small-data lane is recorded"
        ∷ "Clay Navier-Stokes and global regularity promotion flags remain false"
        ∷ []
    }

subcriticalDissipationForAnySPositiveIsNotClaimed :
  subcriticalDissipationForAnySPositive
    canonicalNSSubcriticalDissipationReceipt
  ≡
  false
subcriticalDissipationForAnySPositiveIsNotClaimed =
  refl

nsCarrierThresholdIsRecorded :
  nsCarrierThreshold canonicalNSSubcriticalDissipationReceipt
  ≡
  nsCarrierThresholdText
nsCarrierThresholdIsRecorded =
  refl

subcriticalDissipationForS>=11/8IsSet :
  subcriticalDissipationForS>=11/8
    canonicalNSSubcriticalDissipationReceipt
  ≡
  true
subcriticalDissipationForS>=11/8IsSet =
  refl

belowThresholdSmallDataOnlyIsSet :
  belowThresholdSmallDataOnly canonicalNSSubcriticalDissipationReceipt
  ≡
  true
belowThresholdSmallDataOnlyIsSet =
  refl

dissipationDominatesStretchingAtHighFrequencyIsSet :
  dissipationDominatesStretchingAtHighFrequency
    canonicalNSSubcriticalDissipationReceipt
  ≡
  true
dissipationDominatesStretchingAtHighFrequencyIsSet =
  refl

nsAdjacentOnlyDissipationDominanceForS>=11/8IsSet :
  nsAdjacentOnlyDissipationDominanceForS>=11/8
    canonicalNSSubcriticalDissipationReceipt
  ≡
  true
nsAdjacentOnlyDissipationDominanceForS>=11/8IsSet =
  refl

nsSubcriticalDissipationDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSSubcriticalDissipationReceipt ≡ false
nsSubcriticalDissipationDoesNotPromoteClay =
  refl

nsSubcriticalDissipationDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSSubcriticalDissipationReceipt ≡ false
nsSubcriticalDissipationDoesNotPromoteGlobalRegularity =
  refl

nsSubcriticalDissipationNoPromotion :
  NSAdjacentDissipationPromotion →
  ⊥
nsSubcriticalDissipationNoPromotion =
  nsAdjacentDissipationPromotionImpossibleHere
