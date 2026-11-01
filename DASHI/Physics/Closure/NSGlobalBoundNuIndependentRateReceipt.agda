module DASHI.Physics.Closure.NSGlobalBoundNuIndependentRateReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes C2 global-bound rate receipt.
--
-- This receipt records the C2 rate audit for the carrier global bound.
-- The cascade rate is recorded as R approx p^-2 and is independent of
-- viscosity.  Therefore the high-band geometric summation constant is also
-- independent of viscosity:
--
--   p^-2 / (1 - p^-2).
--
-- The only place where nu^-1 grows is the low-band cutoff sum.  Its
-- dominant large-nu^-1 factor is
--
--   (C0 / nu)^(11/4).
--
-- This is a rate-accounting receipt only.  Clay Navier-Stokes promotion and
-- global regularity promotion remain false.

data NSGlobalBoundNuIndependentRateStatus : Set where
  c2RateAuditRecorded :
    NSGlobalBoundNuIndependentRateStatus

  cascadeRatePToMinusTwoRecorded :
    NSGlobalBoundNuIndependentRateStatus

  cascadeRateNuIndependent :
    NSGlobalBoundNuIndependentRateStatus

  highBandSummationConstantNuIndependent :
    NSGlobalBoundNuIndependentRateStatus

  onlyLowBandSumGrowsWithNuInverse :
    NSGlobalBoundNuIndependentRateStatus

  dominantLowBandFactorRecorded :
    NSGlobalBoundNuIndependentRateStatus

  highBandAmplificationRecorded :
    NSGlobalBoundNuIndependentRateStatus

  noClayOrGlobalPromotion :
    NSGlobalBoundNuIndependentRateStatus

canonicalNSGlobalBoundNuIndependentRateStatus :
  List NSGlobalBoundNuIndependentRateStatus
canonicalNSGlobalBoundNuIndependentRateStatus =
  c2RateAuditRecorded
  ∷ cascadeRatePToMinusTwoRecorded
  ∷ cascadeRateNuIndependent
  ∷ highBandSummationConstantNuIndependent
  ∷ onlyLowBandSumGrowsWithNuInverse
  ∷ dominantLowBandFactorRecorded
  ∷ highBandAmplificationRecorded
  ∷ noClayOrGlobalPromotion
  ∷ []

data NSRateFormula : Set where
  rApproximatelyPToMinusTwo :
    NSRateFormula

data NSHighBandSummationConstant : Set where
  pToMinusTwoOverOneMinusPToMinusTwo :
    NSHighBandSummationConstant

data NSNuGrowthSource : Set where
  lowBandCutoffSumOnly :
    NSNuGrowthSource

data NSDominantNuInverseFactor : Set where
  c0OverNuToElevenOverFourLowBandFactor :
    NSDominantNuInverseFactor

data NSRateTableRow : Set where
  p2AmplificationOneThird :
    NSRateTableRow

  p3AmplificationOneEighth :
    NSRateTableRow

  p7AmplificationOneFortyEighth :
    NSRateTableRow

canonicalNSRateTable :
  List NSRateTableRow
canonicalNSRateTable =
  p2AmplificationOneThird
  ∷ p3AmplificationOneEighth
  ∷ p7AmplificationOneFortyEighth
  ∷ []

data NSGlobalBoundNuIndependentRatePromotion : Set where

nsGlobalBoundNuIndependentRatePromotionImpossibleHere :
  NSGlobalBoundNuIndependentRatePromotion →
  ⊥
nsGlobalBoundNuIndependentRatePromotionImpossibleHere ()

cascadeRateLabel : String
cascadeRateLabel =
  "R approx p^-2"

cascadeRateNuIndependenceLabel : String
cascadeRateNuIndependenceLabel =
  "The cascade rate R approx p^-2 contains no nu factor."

highBandSummationConstantLabel : String
highBandSummationConstantLabel =
  "sum amplification = p^-2/(1-p^-2)"

highBandSummationConstantNuIndependenceLabel : String
highBandSummationConstantNuIndependenceLabel =
  "The high-band summation constant p^-2/(1-p^-2) is nu-independent."

lowBandNuGrowthLabel : String
lowBandNuGrowthLabel =
  "Only the finite low-band cutoff sum grows with nu^-1."

dominantLowBandFactorLabel : String
dominantLowBandFactorLabel =
  "(C0/nu)^(11/4)"

rateTableLabel : String
rateTableLabel =
  "p=2: 1/3; p=3: 1/8; p=7: 1/48 for p^-2/(1-p^-2)"

nsGlobalBoundNuIndependentRateStatement : String
nsGlobalBoundNuIndependentRateStatement =
  "C2 rate receipt: the cascade rate R approx p^-2 is independent of nu; the high-band summation constant is p^-2/(1-p^-2), also nu-independent.  The only nu^-1 growth comes from the finite low-band cutoff sum, whose dominant large-nu^-1 factor is (C0/nu)^(11/4).  High-band amplification is p^-2/(1-p^-2), with p=2 giving 1/3, p=3 giving 1/8, and p=7 giving 1/48.  Clay Navier-Stokes promotion remains false."

record NSGlobalBoundNuIndependentRateReceipt : Setω where
  field
    status :
      List NSGlobalBoundNuIndependentRateStatus

    statusIsCanonical :
      status ≡ canonicalNSGlobalBoundNuIndependentRateStatus

    cascadeRate :
      NSRateFormula

    cascadeRateIsPToMinusTwo :
      cascadeRate ≡ rApproximatelyPToMinusTwo

    cascadeRateFormulaLabel :
      String

    cascadeRateFormulaLabelIsCanonical :
      cascadeRateFormulaLabel ≡ cascadeRateLabel

    cascadeRateDependsOnNu :
      Bool

    cascadeRateDependsOnNuIsFalse :
      cascadeRateDependsOnNu ≡ false

    cascadeRateNuIndependence :
      String

    cascadeRateNuIndependenceIsCanonical :
      cascadeRateNuIndependence ≡ cascadeRateNuIndependenceLabel

    highBandSummationConstant :
      NSHighBandSummationConstant

    highBandSummationConstantIsCanonical :
      highBandSummationConstant ≡ pToMinusTwoOverOneMinusPToMinusTwo

    highBandAmplificationLabel :
      String

    highBandAmplificationLabelIsCanonical :
      highBandAmplificationLabel ≡ highBandSummationConstantLabel

    highBandSummationConstantDependsOnNu :
      Bool

    highBandSummationConstantDependsOnNuIsFalse :
      highBandSummationConstantDependsOnNu ≡ false

    highBandSummationConstantNuIndependence :
      String

    highBandSummationConstantNuIndependenceIsCanonical :
      highBandSummationConstantNuIndependence
      ≡
      highBandSummationConstantNuIndependenceLabel

    nuInverseGrowthSource :
      NSNuGrowthSource

    nuInverseGrowthSourceIsLowBandOnly :
      nuInverseGrowthSource ≡ lowBandCutoffSumOnly

    lowBandNuGrowth :
      String

    lowBandNuGrowthIsCanonical :
      lowBandNuGrowth ≡ lowBandNuGrowthLabel

    onlyLowBandSumGrowsWithNuInverseFlag :
      Bool

    onlyLowBandSumGrowsWithNuInverseFlagIsTrue :
      onlyLowBandSumGrowsWithNuInverseFlag ≡ true

    dominantLargeNuInverseFactor :
      NSDominantNuInverseFactor

    dominantLargeNuInverseFactorIsCanonical :
      dominantLargeNuInverseFactor
      ≡
      c0OverNuToElevenOverFourLowBandFactor

    dominantLargeNuInverseFactorLabel :
      String

    dominantLargeNuInverseFactorLabelIsCanonical :
      dominantLargeNuInverseFactorLabel ≡ dominantLowBandFactorLabel

    dominantTermIsLowBand :
      Bool

    dominantTermIsLowBandIsTrue :
      dominantTermIsLowBand ≡ true

    highBandAmplificationDependsOnNu :
      Bool

    highBandAmplificationDependsOnNuIsFalse :
      highBandAmplificationDependsOnNu ≡ false

    rateTable :
      List NSRateTableRow

    rateTableIsCanonical :
      rateTable ≡ canonicalNSRateTable

    rateTableDescription :
      String

    rateTableDescriptionIsCanonical :
      rateTableDescription ≡ rateTableLabel

    p2 :
      Nat

    p2Is2 :
      p2 ≡ 2

    p3 :
      Nat

    p3Is3 :
      p3 ≡ 3

    p7 :
      Nat

    p7Is7 :
      p7 ≡ 7

    p2AmplificationNumerator :
      Nat

    p2AmplificationNumeratorIs1 :
      p2AmplificationNumerator ≡ 1

    p2AmplificationDenominator :
      Nat

    p2AmplificationDenominatorIs3 :
      p2AmplificationDenominator ≡ 3

    p3AmplificationNumerator :
      Nat

    p3AmplificationNumeratorIs1 :
      p3AmplificationNumerator ≡ 1

    p3AmplificationDenominator :
      Nat

    p3AmplificationDenominatorIs8 :
      p3AmplificationDenominator ≡ 8

    p7AmplificationNumerator :
      Nat

    p7AmplificationNumeratorIs1 :
      p7AmplificationNumerator ≡ 1

    p7AmplificationDenominator :
      Nat

    p7AmplificationDenominatorIs48 :
      p7AmplificationDenominator ≡ 48

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
      statement ≡ nsGlobalBoundNuIndependentRateStatement

    promotionFlags :
      List NSGlobalBoundNuIndependentRatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSGlobalBoundNuIndependentRateReceipt public

canonicalNSGlobalBoundNuIndependentRateReceipt :
  NSGlobalBoundNuIndependentRateReceipt
canonicalNSGlobalBoundNuIndependentRateReceipt =
  record
    { status =
        canonicalNSGlobalBoundNuIndependentRateStatus
    ; statusIsCanonical =
        refl
    ; cascadeRate =
        rApproximatelyPToMinusTwo
    ; cascadeRateIsPToMinusTwo =
        refl
    ; cascadeRateFormulaLabel =
        cascadeRateLabel
    ; cascadeRateFormulaLabelIsCanonical =
        refl
    ; cascadeRateDependsOnNu =
        false
    ; cascadeRateDependsOnNuIsFalse =
        refl
    ; cascadeRateNuIndependence =
        cascadeRateNuIndependenceLabel
    ; cascadeRateNuIndependenceIsCanonical =
        refl
    ; highBandSummationConstant =
        pToMinusTwoOverOneMinusPToMinusTwo
    ; highBandSummationConstantIsCanonical =
        refl
    ; highBandAmplificationLabel =
        highBandSummationConstantLabel
    ; highBandAmplificationLabelIsCanonical =
        refl
    ; highBandSummationConstantDependsOnNu =
        false
    ; highBandSummationConstantDependsOnNuIsFalse =
        refl
    ; highBandSummationConstantNuIndependence =
        highBandSummationConstantNuIndependenceLabel
    ; highBandSummationConstantNuIndependenceIsCanonical =
        refl
    ; nuInverseGrowthSource =
        lowBandCutoffSumOnly
    ; nuInverseGrowthSourceIsLowBandOnly =
        refl
    ; lowBandNuGrowth =
        lowBandNuGrowthLabel
    ; lowBandNuGrowthIsCanonical =
        refl
    ; onlyLowBandSumGrowsWithNuInverseFlag =
        true
    ; onlyLowBandSumGrowsWithNuInverseFlagIsTrue =
        refl
    ; dominantLargeNuInverseFactor =
        c0OverNuToElevenOverFourLowBandFactor
    ; dominantLargeNuInverseFactorIsCanonical =
        refl
    ; dominantLargeNuInverseFactorLabel =
        dominantLowBandFactorLabel
    ; dominantLargeNuInverseFactorLabelIsCanonical =
        refl
    ; dominantTermIsLowBand =
        true
    ; dominantTermIsLowBandIsTrue =
        refl
    ; highBandAmplificationDependsOnNu =
        false
    ; highBandAmplificationDependsOnNuIsFalse =
        refl
    ; rateTable =
        canonicalNSRateTable
    ; rateTableIsCanonical =
        refl
    ; rateTableDescription =
        rateTableLabel
    ; rateTableDescriptionIsCanonical =
        refl
    ; p2 =
        2
    ; p2Is2 =
        refl
    ; p3 =
        3
    ; p3Is3 =
        refl
    ; p7 =
        7
    ; p7Is7 =
        refl
    ; p2AmplificationNumerator =
        1
    ; p2AmplificationNumeratorIs1 =
        refl
    ; p2AmplificationDenominator =
        3
    ; p2AmplificationDenominatorIs3 =
        refl
    ; p3AmplificationNumerator =
        1
    ; p3AmplificationNumeratorIs1 =
        refl
    ; p3AmplificationDenominator =
        8
    ; p3AmplificationDenominatorIs8 =
        refl
    ; p7AmplificationNumerator =
        1
    ; p7AmplificationNumeratorIs1 =
        refl
    ; p7AmplificationDenominator =
        48
    ; p7AmplificationDenominatorIs48 =
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
        nsGlobalBoundNuIndependentRateStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "C2 records rate accounting only"
        ∷ "Cascade rate R approx p^-2 is nu-independent"
        ∷ "High-band summation constant p^-2/(1-p^-2) is nu-independent"
        ∷ "Only the low-band cutoff sum grows with nu^-1"
        ∷ "Dominant large-nu^-1 term is the low-band factor (C0/nu)^(11/4)"
        ∷ "High-band amplification p^-2/(1-p^-2) gives p=2 -> 1/3, p=3 -> 1/8, p=7 -> 1/48"
        ∷ "Clay Navier-Stokes promotion remains false"
        ∷ []
    }

cascadeRateNuIndependentRecorded :
  cascadeRateDependsOnNu canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  false
cascadeRateNuIndependentRecorded =
  refl

highBandSummationConstantNuIndependentRecorded :
  highBandSummationConstantDependsOnNu
    canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  false
highBandSummationConstantNuIndependentRecorded =
  refl

onlyLowBandSumGrowsWithNuInverseRecorded :
  onlyLowBandSumGrowsWithNuInverseFlag
    canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  true
onlyLowBandSumGrowsWithNuInverseRecorded =
  refl

dominantLargeNuInverseFactorRecorded :
  dominantLargeNuInverseFactor
    canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  c0OverNuToElevenOverFourLowBandFactor
dominantLargeNuInverseFactorRecorded =
  refl

highBandAmplificationNuIndependentRecorded :
  highBandAmplificationDependsOnNu
    canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  false
highBandAmplificationNuIndependentRecorded =
  refl

p2HighBandAmplificationRecorded :
  p2AmplificationDenominator canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  3
p2HighBandAmplificationRecorded =
  refl

p3HighBandAmplificationRecorded :
  p3AmplificationDenominator canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  8
p3HighBandAmplificationRecorded =
  refl

p7HighBandAmplificationRecorded :
  p7AmplificationDenominator canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  48
p7HighBandAmplificationRecorded =
  refl

clayNavierStokesPromotedFalse :
  clayNavierStokesPromoted canonicalNSGlobalBoundNuIndependentRateReceipt
  ≡
  false
clayNavierStokesPromotedFalse =
  refl
