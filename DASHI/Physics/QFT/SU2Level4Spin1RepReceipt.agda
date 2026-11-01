module DASHI.Physics.QFT.SU2Level4Spin1RepReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SU(2)_4 spin-representation receipt.
--
-- This receipt records the integrable SU(2)_4 Chern-Simons/WZW boundary
-- sectors j = 0, 1/2, 1, 3/2, 2.  The WZW conformal weight is kept under the
-- standard KZ/WZW convention
--
--   h_j = j(j+1)/(k+2).
--
-- With doubled-spin labels n = 2j this is n(n+2)/(4(k+2)), so at k=4 the
-- j=2 sector has h=1.  The separate diagnostic convention requested by the
-- user, C2/(2(N+k)), gives j=2 -> 1/2 for N=2 and k=4.  These readings are
-- deliberately separated below: wzwConformalWeight records the boundary CFT
-- value, while statisticsParityDiagnostic records only the alternative
-- parity diagnostic.  No Standard Model, G_DHR, or unconditional fermion
-- promotion is claimed here.

su2Level4 :
  Nat
su2Level4 =
  4

su2RankN :
  Nat
su2RankN =
  2

data SU2Level4Representation : Set where
  j0Rep :
    SU2Level4Representation

  j1/2Rep :
    SU2Level4Representation

  j1Rep :
    SU2Level4Representation

  j3/2Rep :
    SU2Level4Representation

  j2Rep :
    SU2Level4Representation

canonicalSU2Level4Representations :
  List SU2Level4Representation
canonicalSU2Level4Representations =
  j0Rep
  ∷ j1/2Rep
  ∷ j1Rep
  ∷ j3/2Rep
  ∷ j2Rep
  ∷ []

doubledSpin :
  SU2Level4Representation →
  Nat
doubledSpin j0Rep =
  0
doubledSpin j1/2Rep =
  1
doubledSpin j1Rep =
  2
doubledSpin j3/2Rep =
  3
doubledSpin j2Rep =
  4

representationLabel :
  SU2Level4Representation →
  String
representationLabel j0Rep =
  "j=0"
representationLabel j1/2Rep =
  "j=1/2"
representationLabel j1Rep =
  "j=1"
representationLabel j3/2Rep =
  "j=3/2"
representationLabel j2Rep =
  "j=2"

record RationalReceipt : Set where
  field
    numerator :
      Nat

    denominator :
      Nat

    reducedLabel :
      String

open RationalReceipt public

wzwConformalWeightNumerator :
  SU2Level4Representation →
  Nat
wzwConformalWeightNumerator rep =
  doubledSpin rep * (doubledSpin rep + 2)

wzwConformalWeightDenominator :
  Nat
wzwConformalWeightDenominator =
  4 * (su2Level4 + 2)

wzwConformalWeightLabel :
  SU2Level4Representation →
  String
wzwConformalWeightLabel j0Rep =
  "h=0"
wzwConformalWeightLabel j1/2Rep =
  "h=1/8"
wzwConformalWeightLabel j1Rep =
  "h=1/3"
wzwConformalWeightLabel j3/2Rep =
  "h=5/8"
wzwConformalWeightLabel j2Rep =
  "h=1"

wzwConformalWeight :
  SU2Level4Representation →
  RationalReceipt
wzwConformalWeight rep =
  record
    { numerator =
        wzwConformalWeightNumerator rep
    ; denominator =
        wzwConformalWeightDenominator
    ; reducedLabel =
        wzwConformalWeightLabel rep
    }

statisticsParityDiagnosticNumerator :
  SU2Level4Representation →
  Nat
statisticsParityDiagnosticNumerator rep =
  doubledSpin rep * (doubledSpin rep + 2)

statisticsParityDiagnosticDenominator :
  Nat
statisticsParityDiagnosticDenominator =
  4 * (2 * (su2RankN + su2Level4))

statisticsParityDiagnosticLabel :
  SU2Level4Representation →
  String
statisticsParityDiagnosticLabel j0Rep =
  "h_diag=0"
statisticsParityDiagnosticLabel j1/2Rep =
  "h_diag=1/16"
statisticsParityDiagnosticLabel j1Rep =
  "h_diag=1/6"
statisticsParityDiagnosticLabel j3/2Rep =
  "h_diag=5/16"
statisticsParityDiagnosticLabel j2Rep =
  "h_diag=1/2"

statisticsParityDiagnostic :
  SU2Level4Representation →
  RationalReceipt
statisticsParityDiagnostic rep =
  record
    { numerator =
        statisticsParityDiagnosticNumerator rep
    ; denominator =
        statisticsParityDiagnosticDenominator
    ; reducedLabel =
        statisticsParityDiagnosticLabel rep
    }

wzwFormulaLabel :
  String
wzwFormulaLabel =
  "WZW/KZ boundary conformal weight: h_j = j(j+1)/(k+2)"

statisticsDiagnosticFormulaLabel :
  String
statisticsDiagnosticFormulaLabel =
  "statistics parity diagnostic only: C2/(2(N+k))"

j2ConventionResolutionLabel :
  String
j2ConventionResolutionLabel =
  "at SU(2)_4, j=2 has WZW h=1; the separate C2/(2(N+k)) diagnostic gives 1/2"

failClosedBoundaryLabel :
  String
failClosedBoundaryLabel =
  "receipt is diagnostic and fail-closed: no SM, G_DHR, or unconditional fermion promotion"

record SU2Level4Spin1RepReceipt : Setω where
  field
    level :
      Nat

    levelIsFour :
      level ≡ su2Level4

    rankN :
      Nat

    rankNIsTwo :
      rankN ≡ su2RankN

    representations :
      List SU2Level4Representation

    representationsAreCanonical :
      representations ≡ canonicalSU2Level4Representations

    wzwFormula :
      String

    wzwFormulaIsCanonical :
      wzwFormula ≡ wzwFormulaLabel

    j0WZWWeight :
      RationalReceipt

    j0WZWWeightIsCanonical :
      j0WZWWeight ≡ wzwConformalWeight j0Rep

    j1/2WZWWeight :
      RationalReceipt

    j1/2WZWWeightIsCanonical :
      j1/2WZWWeight ≡ wzwConformalWeight j1/2Rep

    j1WZWWeight :
      RationalReceipt

    j1WZWWeightIsCanonical :
      j1WZWWeight ≡ wzwConformalWeight j1Rep

    j3/2WZWWeight :
      RationalReceipt

    j3/2WZWWeightIsCanonical :
      j3/2WZWWeight ≡ wzwConformalWeight j3/2Rep

    j2WZWWeight :
      RationalReceipt

    j2WZWWeightIsCanonical :
      j2WZWWeight ≡ wzwConformalWeight j2Rep

    j2WZWLabel :
      String

    j2WZWLabelIsOne :
      j2WZWLabel ≡ "h=1"

    statisticsDiagnosticFormula :
      String

    statisticsDiagnosticFormulaIsCanonical :
      statisticsDiagnosticFormula ≡ statisticsDiagnosticFormulaLabel

    j2StatisticsParityDiagnostic :
      RationalReceipt

    j2StatisticsParityDiagnosticIsCanonical :
      j2StatisticsParityDiagnostic ≡ statisticsParityDiagnostic j2Rep

    j2StatisticsParityDiagnosticLabel :
      String

    j2StatisticsParityDiagnosticLabelIsHalf :
      j2StatisticsParityDiagnosticLabel ≡ "h_diag=1/2"

    conventionResolvedBySeparation :
      Bool

    conventionResolvedBySeparationIsTrue :
      conventionResolvedBySeparation ≡ true

    conventionResolutionBoundary :
      String

    conventionResolutionBoundaryIsCanonical :
      conventionResolutionBoundary ≡ j2ConventionResolutionLabel

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

    unconditionalFermionPromotion :
      Bool

    unconditionalFermionPromotionIsFalse :
      unconditionalFermionPromotion ≡ false

    failClosedBoundary :
      String

    failClosedBoundaryIsCanonical :
      failClosedBoundary ≡ failClosedBoundaryLabel

    receiptBoundary :
      List String

open SU2Level4Spin1RepReceipt public

canonicalSU2Level4Spin1RepReceipt :
  SU2Level4Spin1RepReceipt
canonicalSU2Level4Spin1RepReceipt =
  record
    { level =
        su2Level4
    ; levelIsFour =
        refl
    ; rankN =
        su2RankN
    ; rankNIsTwo =
        refl
    ; representations =
        canonicalSU2Level4Representations
    ; representationsAreCanonical =
        refl
    ; wzwFormula =
        wzwFormulaLabel
    ; wzwFormulaIsCanonical =
        refl
    ; j0WZWWeight =
        wzwConformalWeight j0Rep
    ; j0WZWWeightIsCanonical =
        refl
    ; j1/2WZWWeight =
        wzwConformalWeight j1/2Rep
    ; j1/2WZWWeightIsCanonical =
        refl
    ; j1WZWWeight =
        wzwConformalWeight j1Rep
    ; j1WZWWeightIsCanonical =
        refl
    ; j3/2WZWWeight =
        wzwConformalWeight j3/2Rep
    ; j3/2WZWWeightIsCanonical =
        refl
    ; j2WZWWeight =
        wzwConformalWeight j2Rep
    ; j2WZWWeightIsCanonical =
        refl
    ; j2WZWLabel =
        "h=1"
    ; j2WZWLabelIsOne =
        refl
    ; statisticsDiagnosticFormula =
        statisticsDiagnosticFormulaLabel
    ; statisticsDiagnosticFormulaIsCanonical =
        refl
    ; j2StatisticsParityDiagnostic =
        statisticsParityDiagnostic j2Rep
    ; j2StatisticsParityDiagnosticIsCanonical =
        refl
    ; j2StatisticsParityDiagnosticLabel =
        "h_diag=1/2"
    ; j2StatisticsParityDiagnosticLabelIsHalf =
        refl
    ; conventionResolvedBySeparation =
        true
    ; conventionResolvedBySeparationIsTrue =
        refl
    ; conventionResolutionBoundary =
        j2ConventionResolutionLabel
    ; conventionResolutionBoundaryIsCanonical =
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
    ; unconditionalFermionPromotion =
        false
    ; unconditionalFermionPromotionIsFalse =
        refl
    ; failClosedBoundary =
        failClosedBoundaryLabel
    ; failClosedBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        wzwFormulaLabel
        ∷ statisticsDiagnosticFormulaLabel
        ∷ j2ConventionResolutionLabel
        ∷ failClosedBoundaryLabel
        ∷ []
    }

su2Level4Spin1RepRepresentationsCanonical :
  representations canonicalSU2Level4Spin1RepReceipt
  ≡
  canonicalSU2Level4Representations
su2Level4Spin1RepRepresentationsCanonical =
  refl

su2Level4Spin1RepJ2WZWIsOne :
  j2WZWLabel canonicalSU2Level4Spin1RepReceipt
  ≡
  "h=1"
su2Level4Spin1RepJ2WZWIsOne =
  refl

su2Level4Spin1RepJ2DiagnosticIsHalf :
  j2StatisticsParityDiagnosticLabel canonicalSU2Level4Spin1RepReceipt
  ≡
  "h_diag=1/2"
su2Level4Spin1RepJ2DiagnosticIsHalf =
  refl

su2Level4Spin1RepConventionResolved :
  conventionResolvedBySeparation canonicalSU2Level4Spin1RepReceipt
  ≡
  true
su2Level4Spin1RepConventionResolved =
  refl

su2Level4Spin1RepExactStandardModelPromotionFalse :
  exactStandardModelPromotion canonicalSU2Level4Spin1RepReceipt
  ≡
  false
su2Level4Spin1RepExactStandardModelPromotionFalse =
  refl

su2Level4Spin1RepExactGDHRPromotionFalse :
  exactGDHRPromotion canonicalSU2Level4Spin1RepReceipt
  ≡
  false
su2Level4Spin1RepExactGDHRPromotionFalse =
  refl

su2Level4Spin1RepExactGDHREqualsGSMPromotionFalse :
  exactGDHREqualsGSMPromotion canonicalSU2Level4Spin1RepReceipt
  ≡
  false
su2Level4Spin1RepExactGDHREqualsGSMPromotionFalse =
  refl

su2Level4Spin1RepUnconditionalFermionPromotionFalse :
  unconditionalFermionPromotion canonicalSU2Level4Spin1RepReceipt
  ≡
  false
su2Level4Spin1RepUnconditionalFermionPromotionFalse =
  refl
