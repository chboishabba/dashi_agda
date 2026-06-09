module DASHI.Physics.Closure.NSHighBandGeometricSumReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes high-band geometric-sum receipt.
--
-- This receipt records the A3 high-band summation shape:
--
--   e_j <= 2 e_j(0) + 2 C^2/(nu^2 p^{2j}) e_{j_nu}
--
-- Hence, for E_high = sum_{j > j_nu} e_j,
--
--   E_high <= 2 E(0)
--             + (2 C^2/nu^2) e_{j_nu}
--               sum_{j > j_nu} p^{-2j}
--
-- and the tail is the convergent geometric series
--
--   p^{-2(j_nu+1)} / (1 - p^{-2}).
--
-- With e_{j_nu} <= p^{11 j_nu/4} M_0^2, the high-band constant is finite
-- for every nu > 0.  This is only a high-band bound receipt; it creates no
-- Clay Navier-Stokes or global-regularity promotion.

data NSHighBandGeometricSumStatus : Set where
  a3HighBandEstimateRecorded :
    NSHighBandGeometricSumStatus

  highBandEnergyTailRecorded :
    NSHighBandGeometricSumStatus

  geometricSeriesFormulaRecorded :
    NSHighBandGeometricSumStatus

  jNuEnergyH118ControlRecorded :
    NSHighBandGeometricSumStatus

  highBandConstantFiniteForNuPositive :
    NSHighBandGeometricSumStatus

  noClayPromotion :
    NSHighBandGeometricSumStatus

canonicalNSHighBandGeometricSumStatus :
  List NSHighBandGeometricSumStatus
canonicalNSHighBandGeometricSumStatus =
  a3HighBandEstimateRecorded
  ∷ highBandEnergyTailRecorded
  ∷ geometricSeriesFormulaRecorded
  ∷ jNuEnergyH118ControlRecorded
  ∷ highBandConstantFiniteForNuPositive
  ∷ noClayPromotion
  ∷ []

data NSHighBandBoundFormula : Set where
  twoE0PlusCHighNuM0 :
    NSHighBandBoundFormula

data NSGeometricSeriesFormula : Set where
  pToMinusTwoJNuPlusOneOverOneMinusPToMinusTwo :
    NSGeometricSeriesFormula

data NSHighBandPromotion : Set where

nsHighBandPromotionImpossibleHere :
  NSHighBandPromotion →
  ⊥
nsHighBandPromotionImpossibleHere ()

nsHighBandPointwiseEstimate : String
nsHighBandPointwiseEstimate =
  "e_j <= 2 e_j(0)+2 C^2/(nu^2 p^{2j}) e_{j_nu}"

nsHighBandTailEstimate : String
nsHighBandTailEstimate =
  "E_high = sum_{j>j_nu} e_j <= 2E(0)+(2C^2/nu^2)e_{j_nu} sum_{j>j_nu} p^{-2j}"

nsHighBandGeometricSeries : String
nsHighBandGeometricSeries =
  "sum_{j>j_nu} p^{-2j} = p^{-2(j_nu+1)}/(1-p^{-2})"

nsHighBandJNuEnergyBound : String
nsHighBandJNuEnergyBound =
  "e_{j_nu} <= p^{11 j_nu/4} M_0^2"

nsHighBandBoundLabel : String
nsHighBandBoundLabel =
  "2E(0)+C_high(nu,M0)"

nsHighBandStatement : String
nsHighBandStatement =
  "A3 high-band receipt: the pointwise estimate e_j <= 2 e_j(0)+2 C^2/(nu^2 p^{2j}) e_{j_nu} gives E_high <= 2E(0)+(2C^2/nu^2)e_{j_nu} sum_{j>j_nu}p^{-2j}; the geometric sum is p^{-2(j_nu+1)}/(1-p^{-2}); using e_{j_nu} <= p^{11 j_nu/4} M_0^2 yields a finite C_high for every nu > 0.  No Clay promotion follows."

record NSHighBandGeometricSumReceipt : Setω where
  field
    status :
      List NSHighBandGeometricSumStatus

    statusIsCanonical :
      status ≡ canonicalNSHighBandGeometricSumStatus

    pointwiseEstimate :
      String

    pointwiseEstimateIsCanonical :
      pointwiseEstimate ≡ nsHighBandPointwiseEstimate

    highBandTailEstimate :
      String

    highBandTailEstimateIsCanonical :
      highBandTailEstimate ≡ nsHighBandTailEstimate

    geometricSeriesFormula :
      NSGeometricSeriesFormula

    geometricSeriesFormulaIsCanonical :
      geometricSeriesFormula
      ≡
      pToMinusTwoJNuPlusOneOverOneMinusPToMinusTwo

    geometricSeriesFormulaLabel :
      String

    geometricSeriesFormulaLabelIsCanonical :
      geometricSeriesFormulaLabel ≡ nsHighBandGeometricSeries

    geometricSeriesConverges :
      Bool

    geometricSeriesConvergesIsTrue :
      geometricSeriesConverges ≡ true

    jNuEnergyBound :
      String

    jNuEnergyBoundIsCanonical :
      jNuEnergyBound ≡ nsHighBandJNuEnergyBound

    eJNuControlledByH118M0 :
      Bool

    eJNuControlledByH118M0IsTrue :
      eJNuControlledByH118M0 ≡ true

    h118Numerator :
      Nat

    h118NumeratorIs11 :
      h118Numerator ≡ 11

    h118Denominator :
      Nat

    h118DenominatorIs8 :
      h118Denominator ≡ 8

    jNuEnergyExponentNumerator :
      Nat

    jNuEnergyExponentNumeratorIs11 :
      jNuEnergyExponentNumerator ≡ 11

    jNuEnergyExponentDenominator :
      Nat

    jNuEnergyExponentDenominatorIs4 :
      jNuEnergyExponentDenominator ≡ 4

    nuPositiveAssumptionRecorded :
      Bool

    nuPositiveAssumptionRecordedIsTrue :
      nuPositiveAssumptionRecorded ≡ true

    cHighFiniteForAnyNuPositive :
      Bool

    cHighFiniteForAnyNuPositiveIsTrue :
      cHighFiniteForAnyNuPositive ≡ true

    highBandBoundFormula :
      NSHighBandBoundFormula

    highBandBoundFormulaIsCanonical :
      highBandBoundFormula ≡ twoE0PlusCHighNuM0

    highBandBound :
      String

    highBandBoundIsCanonical :
      highBandBound ≡ nsHighBandBoundLabel

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayPromotionAttempted :
      Bool

    clayPromotionAttemptedIsFalse :
      clayPromotionAttempted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsHighBandStatement

    promotionFlags :
      List NSHighBandPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSHighBandGeometricSumReceipt public

canonicalNSHighBandGeometricSumReceipt :
  NSHighBandGeometricSumReceipt
canonicalNSHighBandGeometricSumReceipt =
  record
    { status =
        canonicalNSHighBandGeometricSumStatus
    ; statusIsCanonical =
        refl
    ; pointwiseEstimate =
        nsHighBandPointwiseEstimate
    ; pointwiseEstimateIsCanonical =
        refl
    ; highBandTailEstimate =
        nsHighBandTailEstimate
    ; highBandTailEstimateIsCanonical =
        refl
    ; geometricSeriesFormula =
        pToMinusTwoJNuPlusOneOverOneMinusPToMinusTwo
    ; geometricSeriesFormulaIsCanonical =
        refl
    ; geometricSeriesFormulaLabel =
        nsHighBandGeometricSeries
    ; geometricSeriesFormulaLabelIsCanonical =
        refl
    ; geometricSeriesConverges =
        true
    ; geometricSeriesConvergesIsTrue =
        refl
    ; jNuEnergyBound =
        nsHighBandJNuEnergyBound
    ; jNuEnergyBoundIsCanonical =
        refl
    ; eJNuControlledByH118M0 =
        true
    ; eJNuControlledByH118M0IsTrue =
        refl
    ; h118Numerator =
        11
    ; h118NumeratorIs11 =
        refl
    ; h118Denominator =
        8
    ; h118DenominatorIs8 =
        refl
    ; jNuEnergyExponentNumerator =
        11
    ; jNuEnergyExponentNumeratorIs11 =
        refl
    ; jNuEnergyExponentDenominator =
        4
    ; jNuEnergyExponentDenominatorIs4 =
        refl
    ; nuPositiveAssumptionRecorded =
        true
    ; nuPositiveAssumptionRecordedIsTrue =
        refl
    ; cHighFiniteForAnyNuPositive =
        true
    ; cHighFiniteForAnyNuPositiveIsTrue =
        refl
    ; highBandBoundFormula =
        twoE0PlusCHighNuM0
    ; highBandBoundFormulaIsCanonical =
        refl
    ; highBandBound =
        nsHighBandBoundLabel
    ; highBandBoundIsCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayPromotionAttempted =
        false
    ; clayPromotionAttemptedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; statement =
        nsHighBandStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records the A3 pointwise high-band estimate"
        ∷ "Records E_high <= 2E(0)+(2C^2/nu^2)e_{j_nu} sum_{j>j_nu} p^{-2j}"
        ∷ "Records sum_{j>j_nu}p^{-2j} = p^{-2(j_nu+1)}/(1-p^{-2})"
        ∷ "Records geometricSeriesConverges = true"
        ∷ "Records e_{j_nu} <= p^{11 j_nu/4} M_0^2"
        ∷ "Records highBandBound = 2E(0)+C_high(nu,M0)"
        ∷ "No Clay or global-regularity promotion is made"
        ∷ []
    }

highBandBoundIsCanonicalLabel :
  highBandBound canonicalNSHighBandGeometricSumReceipt
    ≡
    "2E(0)+C_high(nu,M0)"
highBandBoundIsCanonicalLabel =
  refl

geometricSeriesConvergesTrue :
  geometricSeriesConverges canonicalNSHighBandGeometricSumReceipt
    ≡
    true
geometricSeriesConvergesTrue =
  refl

cHighFiniteForNuPositive :
  cHighFiniteForAnyNuPositive canonicalNSHighBandGeometricSumReceipt
    ≡
    true
cHighFiniteForNuPositive =
  refl

nsHighBandDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSHighBandGeometricSumReceipt
    ≡
    false
nsHighBandDoesNotPromoteClay =
  refl

nsHighBandDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSHighBandGeometricSumReceipt
    ≡
    false
nsHighBandDoesNotPromoteGlobalRegularity =
  refl

nsHighBandNoPromotion :
  NSHighBandPromotion →
  ⊥
nsHighBandNoPromotion =
  nsHighBandPromotionImpossibleHere
