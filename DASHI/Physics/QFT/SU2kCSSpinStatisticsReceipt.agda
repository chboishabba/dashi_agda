module DASHI.Physics.QFT.SU2kCSSpinStatisticsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SU(2)_k Chern-Simons spin-statistics diagnostic receipt.
--
-- This receipt records the diagnostic convention h = C2(rep)/(2k).  It is
-- not a promotion receipt: the fundamental representation does not give
-- h=1/2 for k=1,2,4 under the recorded normalization, while the spin-1
-- representation at k=4 does give h=1/2.  The conductor-4 p2 lane is recorded
-- only as a candidate source for SU(2)_4 data.  All Standard Model and G_DHR
-- promotion flags remain false.

data SU2kLevel : Set where
  k1 :
    SU2kLevel

  k2 :
    SU2kLevel

  k4 :
    SU2kLevel

canonicalSU2kDiagnosticLevels :
  List SU2kLevel
canonicalSU2kDiagnosticLevels =
  k1
  ∷ k2
  ∷ k4
  ∷ []

su2kLevelValue :
  SU2kLevel →
  Nat
su2kLevelValue k1 =
  1
su2kLevelValue k2 =
  2
su2kLevelValue k4 =
  4

data SU2Representation : Set where
  fundamentalRep :
    SU2Representation

  spin1Rep :
    SU2Representation

su2RepresentationLabel :
  SU2Representation →
  String
su2RepresentationLabel fundamentalRep =
  "fundamental"
su2RepresentationLabel spin1Rep =
  "spin-1"

su2CasimirNumerator :
  SU2Representation →
  Nat
su2CasimirNumerator fundamentalRep =
  3
su2CasimirNumerator spin1Rep =
  4

su2ConformalSpinNumerator :
  SU2Representation →
  Nat
su2ConformalSpinNumerator rep =
  su2CasimirNumerator rep

su2ConformalSpinDenominator :
  SU2kLevel →
  Nat
su2ConformalSpinDenominator k =
  2 * su2kLevelValue k

fundamentalAtK1SpinLabel :
  String
fundamentalAtK1SpinLabel =
  "h=3/2"

fundamentalAtK2SpinLabel :
  String
fundamentalAtK2SpinLabel =
  "h=3/4"

fundamentalAtK4SpinLabel :
  String
fundamentalAtK4SpinLabel =
  "h=3/8"

spin1AtK4SpinLabel :
  String
spin1AtK4SpinLabel =
  "h=1/2"

su2kSpinFormulaLabel :
  String
su2kSpinFormulaLabel =
  "h = C2(rep)/(2k)"

conductor4P2LaneSU24CandidateLabel :
  String
conductor4P2LaneSU24CandidateLabel =
  "conductor-4 p2 lane is a candidate source for SU(2)_4 spin-statistics data"

fundamentalK124NoHalfLabel :
  String
fundamentalK124NoHalfLabel =
  "fundamental rep at k=1,2,4 gives h=3/2,3/4,3/8, so none is h=1/2"

spin1K4HalfLabel :
  String
spin1K4HalfLabel =
  "spin-1 rep at k=4 gives h=1/2"

allPromotionsFalseLabel :
  String
allPromotionsFalseLabel =
  "all Standard Model and G_DHR promotions remain false"

record SU2kCSSpinStatisticsReceipt : Setω where
  field
    diagnosticLevels :
      List SU2kLevel

    diagnosticLevelsAreCanonical :
      diagnosticLevels ≡ canonicalSU2kDiagnosticLevels

    spinFormula :
      String

    spinFormulaIsCanonical :
      spinFormula ≡ su2kSpinFormulaLabel

    fundamentalC2Numerator :
      Nat

    fundamentalC2NumeratorIsThree :
      fundamentalC2Numerator ≡ su2CasimirNumerator fundamentalRep

    spin1C2Numerator :
      Nat

    spin1C2NumeratorIsFour :
      spin1C2Numerator ≡ su2CasimirNumerator spin1Rep

    fundamentalAtK1Numerator :
      Nat

    fundamentalAtK1NumeratorIsC2 :
      fundamentalAtK1Numerator ≡ su2ConformalSpinNumerator fundamentalRep

    fundamentalAtK1Denominator :
      Nat

    fundamentalAtK1DenominatorIsTwoK :
      fundamentalAtK1Denominator ≡ su2ConformalSpinDenominator k1

    fundamentalAtK1Label :
      String

    fundamentalAtK1LabelIsCanonical :
      fundamentalAtK1Label ≡ fundamentalAtK1SpinLabel

    fundamentalAtK1IsHalf :
      Bool

    fundamentalAtK1IsHalfIsFalse :
      fundamentalAtK1IsHalf ≡ false

    fundamentalAtK2Numerator :
      Nat

    fundamentalAtK2NumeratorIsC2 :
      fundamentalAtK2Numerator ≡ su2ConformalSpinNumerator fundamentalRep

    fundamentalAtK2Denominator :
      Nat

    fundamentalAtK2DenominatorIsTwoK :
      fundamentalAtK2Denominator ≡ su2ConformalSpinDenominator k2

    fundamentalAtK2Label :
      String

    fundamentalAtK2LabelIsCanonical :
      fundamentalAtK2Label ≡ fundamentalAtK2SpinLabel

    fundamentalAtK2IsHalf :
      Bool

    fundamentalAtK2IsHalfIsFalse :
      fundamentalAtK2IsHalf ≡ false

    fundamentalAtK4Numerator :
      Nat

    fundamentalAtK4NumeratorIsC2 :
      fundamentalAtK4Numerator ≡ su2ConformalSpinNumerator fundamentalRep

    fundamentalAtK4Denominator :
      Nat

    fundamentalAtK4DenominatorIsTwoK :
      fundamentalAtK4Denominator ≡ su2ConformalSpinDenominator k4

    fundamentalAtK4Label :
      String

    fundamentalAtK4LabelIsCanonical :
      fundamentalAtK4Label ≡ fundamentalAtK4SpinLabel

    fundamentalAtK4IsHalf :
      Bool

    fundamentalAtK4IsHalfIsFalse :
      fundamentalAtK4IsHalf ≡ false

    fundamentalK124HasAnyHalf :
      Bool

    fundamentalK124HasAnyHalfIsFalse :
      fundamentalK124HasAnyHalf ≡ false

    fundamentalK124NoHalfBoundary :
      String

    fundamentalK124NoHalfBoundaryIsCanonical :
      fundamentalK124NoHalfBoundary ≡ fundamentalK124NoHalfLabel

    spin1AtK4Numerator :
      Nat

    spin1AtK4NumeratorIsC2 :
      spin1AtK4Numerator ≡ su2ConformalSpinNumerator spin1Rep

    spin1AtK4Denominator :
      Nat

    spin1AtK4DenominatorIsTwoK :
      spin1AtK4Denominator ≡ su2ConformalSpinDenominator k4

    spin1AtK4Label :
      String

    spin1AtK4LabelIsCanonical :
      spin1AtK4Label ≡ spin1AtK4SpinLabel

    spin1AtK4IsHalf :
      Bool

    spin1AtK4IsHalfIsTrue :
      spin1AtK4IsHalf ≡ true

    spin1K4HalfBoundary :
      String

    spin1K4HalfBoundaryIsCanonical :
      spin1K4HalfBoundary ≡ spin1K4HalfLabel

    conductor4P2LaneCandidateSU24Source :
      Bool

    conductor4P2LaneCandidateSU24SourceIsTrue :
      conductor4P2LaneCandidateSU24Source ≡ true

    conductor4P2LaneCandidateBoundary :
      String

    conductor4P2LaneCandidateBoundaryIsCanonical :
      conductor4P2LaneCandidateBoundary
      ≡
      conductor4P2LaneSU24CandidateLabel

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHRPromotion :
      Bool

    exactGDHRPromotionIsFalse :
      exactGDHRPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    allSMGDHRPromotionsFalse :
      Bool

    allSMGDHRPromotionsFalseIsTrue :
      allSMGDHRPromotionsFalse ≡ true

    allPromotionsFalseBoundary :
      String

    allPromotionsFalseBoundaryIsCanonical :
      allPromotionsFalseBoundary ≡ allPromotionsFalseLabel

    receiptBoundary :
      List String

open SU2kCSSpinStatisticsReceipt public

canonicalSU2kCSSpinStatisticsReceipt :
  SU2kCSSpinStatisticsReceipt
canonicalSU2kCSSpinStatisticsReceipt =
  record
    { diagnosticLevels =
        canonicalSU2kDiagnosticLevels
    ; diagnosticLevelsAreCanonical =
        refl
    ; spinFormula =
        su2kSpinFormulaLabel
    ; spinFormulaIsCanonical =
        refl
    ; fundamentalC2Numerator =
        su2CasimirNumerator fundamentalRep
    ; fundamentalC2NumeratorIsThree =
        refl
    ; spin1C2Numerator =
        su2CasimirNumerator spin1Rep
    ; spin1C2NumeratorIsFour =
        refl
    ; fundamentalAtK1Numerator =
        su2ConformalSpinNumerator fundamentalRep
    ; fundamentalAtK1NumeratorIsC2 =
        refl
    ; fundamentalAtK1Denominator =
        su2ConformalSpinDenominator k1
    ; fundamentalAtK1DenominatorIsTwoK =
        refl
    ; fundamentalAtK1Label =
        fundamentalAtK1SpinLabel
    ; fundamentalAtK1LabelIsCanonical =
        refl
    ; fundamentalAtK1IsHalf =
        false
    ; fundamentalAtK1IsHalfIsFalse =
        refl
    ; fundamentalAtK2Numerator =
        su2ConformalSpinNumerator fundamentalRep
    ; fundamentalAtK2NumeratorIsC2 =
        refl
    ; fundamentalAtK2Denominator =
        su2ConformalSpinDenominator k2
    ; fundamentalAtK2DenominatorIsTwoK =
        refl
    ; fundamentalAtK2Label =
        fundamentalAtK2SpinLabel
    ; fundamentalAtK2LabelIsCanonical =
        refl
    ; fundamentalAtK2IsHalf =
        false
    ; fundamentalAtK2IsHalfIsFalse =
        refl
    ; fundamentalAtK4Numerator =
        su2ConformalSpinNumerator fundamentalRep
    ; fundamentalAtK4NumeratorIsC2 =
        refl
    ; fundamentalAtK4Denominator =
        su2ConformalSpinDenominator k4
    ; fundamentalAtK4DenominatorIsTwoK =
        refl
    ; fundamentalAtK4Label =
        fundamentalAtK4SpinLabel
    ; fundamentalAtK4LabelIsCanonical =
        refl
    ; fundamentalAtK4IsHalf =
        false
    ; fundamentalAtK4IsHalfIsFalse =
        refl
    ; fundamentalK124HasAnyHalf =
        false
    ; fundamentalK124HasAnyHalfIsFalse =
        refl
    ; fundamentalK124NoHalfBoundary =
        fundamentalK124NoHalfLabel
    ; fundamentalK124NoHalfBoundaryIsCanonical =
        refl
    ; spin1AtK4Numerator =
        su2ConformalSpinNumerator spin1Rep
    ; spin1AtK4NumeratorIsC2 =
        refl
    ; spin1AtK4Denominator =
        su2ConformalSpinDenominator k4
    ; spin1AtK4DenominatorIsTwoK =
        refl
    ; spin1AtK4Label =
        spin1AtK4SpinLabel
    ; spin1AtK4LabelIsCanonical =
        refl
    ; spin1AtK4IsHalf =
        true
    ; spin1AtK4IsHalfIsTrue =
        refl
    ; spin1K4HalfBoundary =
        spin1K4HalfLabel
    ; spin1K4HalfBoundaryIsCanonical =
        refl
    ; conductor4P2LaneCandidateSU24Source =
        true
    ; conductor4P2LaneCandidateSU24SourceIsTrue =
        refl
    ; conductor4P2LaneCandidateBoundary =
        conductor4P2LaneSU24CandidateLabel
    ; conductor4P2LaneCandidateBoundaryIsCanonical =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHRPromotion =
        false
    ; exactGDHRPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; allSMGDHRPromotionsFalse =
        true
    ; allSMGDHRPromotionsFalseIsTrue =
        refl
    ; allPromotionsFalseBoundary =
        allPromotionsFalseLabel
    ; allPromotionsFalseBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        su2kSpinFormulaLabel
        ∷ fundamentalK124NoHalfLabel
        ∷ spin1K4HalfLabel
        ∷ conductor4P2LaneSU24CandidateLabel
        ∷ allPromotionsFalseLabel
        ∷ []
    }

su2kCSSpinStatisticsFundamentalK124HasNoHalf :
  fundamentalK124HasAnyHalf canonicalSU2kCSSpinStatisticsReceipt
  ≡
  false
su2kCSSpinStatisticsFundamentalK124HasNoHalf =
  refl

su2kCSSpinStatisticsSpin1K4IsHalf :
  spin1AtK4IsHalf canonicalSU2kCSSpinStatisticsReceipt
  ≡
  true
su2kCSSpinStatisticsSpin1K4IsHalf =
  refl

su2kCSSpinStatisticsConductor4P2LaneCandidate :
  conductor4P2LaneCandidateSU24Source canonicalSU2kCSSpinStatisticsReceipt
  ≡
  true
su2kCSSpinStatisticsConductor4P2LaneCandidate =
  refl

su2kCSSpinStatisticsExactStandardModelPromotionFalse :
  exactStandardModelPromotion canonicalSU2kCSSpinStatisticsReceipt
  ≡
  false
su2kCSSpinStatisticsExactStandardModelPromotionFalse =
  refl

su2kCSSpinStatisticsExactGDHRPromotionFalse :
  exactGDHRPromotion canonicalSU2kCSSpinStatisticsReceipt
  ≡
  false
su2kCSSpinStatisticsExactGDHRPromotionFalse =
  refl

su2kCSSpinStatisticsExactGDHREqualsGSMPromotionFalse :
  exactGDHREqualsGSMPromotion canonicalSU2kCSSpinStatisticsReceipt
  ≡
  false
su2kCSSpinStatisticsExactGDHREqualsGSMPromotionFalse =
  refl
