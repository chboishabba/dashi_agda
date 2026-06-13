module DASHI.Physics.Closure.YMGeometricTailHalfBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Foundations.RealAnalysisAxioms as RA

------------------------------------------------------------------------
-- YM geometric tail half-bound receipt.
--
-- This module records the local geometric-series tail shape used in the
-- polymer proof step
--
--   r <= 1/4  =>  sum_{n >= 1} r^n <= 1/2
--
-- with the stronger envelope
--
--   sum_{n >= 1} r^n <= 1/3
--
-- also named as a receipt surface.  It does not prove the analytic bound
-- itself, does not derive the real-analysis axioms, and does not promote any
-- YM/KP/Clay conclusion.  The purpose is to keep the closure lane fail-closed
-- while providing a typed local surface for the tail step.

data YMGeometricTailHalfBoundStatus : Set where
  geometricTailHalfBoundReceiptRecorded :
    YMGeometricTailHalfBoundStatus

data YMGeometricTailRatioSurface : Set where
  ratioBoundAtQuarterRecorded :
    YMGeometricTailRatioSurface

data YMGeometricTailSeriesShape : Set where
  geometricSeriesTailStartsAtOneRecorded :
    YMGeometricTailSeriesShape

  geometricSeriesTailUsesPowersOfRRecorded :
    YMGeometricTailSeriesShape

data YMGeometricTailEnvelope : Set where
  tailEnvelopeAtMostHalfRecorded :
    YMGeometricTailEnvelope

  tailEnvelopeAtMostThirdRecorded :
    YMGeometricTailEnvelope

data YMGeometricTailDependency : Set where
  realAnalysisGeometricSeriesAuthority :
    YMGeometricTailDependency

  builtinBoolNatStringEqualitySurface :
    YMGeometricTailDependency

  listLedgerSurface :
    YMGeometricTailDependency

  failClosedReceiptBoundarySurface :
    YMGeometricTailDependency

data YMGeometricTailNonClaim : Set where
  noAnalyticProofOfTheTailInequality :
    YMGeometricTailNonClaim

  noExactNumericalEvaluationOfTheInfiniteSum :
    YMGeometricTailNonClaim

  noKPPromotion :
    YMGeometricTailNonClaim

  noContinuumYangMillsClaim :
    YMGeometricTailNonClaim

  noClayPromotion :
    YMGeometricTailNonClaim

canonicalYMGeometricTailDependencies :
  List YMGeometricTailDependency
canonicalYMGeometricTailDependencies =
  realAnalysisGeometricSeriesAuthority
  ∷ builtinBoolNatStringEqualitySurface
  ∷ listLedgerSurface
  ∷ failClosedReceiptBoundarySurface
  ∷ []

canonicalYMGeometricTailNonClaims :
  List YMGeometricTailNonClaim
canonicalYMGeometricTailNonClaims =
  noAnalyticProofOfTheTailInequality
  ∷ noExactNumericalEvaluationOfTheInfiniteSum
  ∷ noKPPromotion
  ∷ noContinuumYangMillsClaim
  ∷ noClayPromotion
  ∷ []

data YMGeometricTailPromotion : Set where

ymGeometricTailPromotionImpossibleHere :
  YMGeometricTailPromotion →
  ⊥
ymGeometricTailPromotionImpossibleHere ()

quarterRatioNumerator :
  Nat
quarterRatioNumerator =
  1

quarterRatioDenominator :
  Nat
quarterRatioDenominator =
  4

tailHalfNumerator :
  Nat
tailHalfNumerator =
  1

tailHalfDenominator :
  Nat
tailHalfDenominator =
  2

tailThirdNumerator :
  Nat
tailThirdNumerator =
  1

tailThirdDenominator :
  Nat
tailThirdDenominator =
  3

tailShapeStatement :
  String
tailShapeStatement =
  "Geometric tail shape recorded as sum_{n>=1} r^n with the standard r/(1-r) envelope; the receipt names the r <= 1/4 hypothesis surface, the <= 1/2 conclusion surface, and the stronger <= 1/3 envelope."

tailBoundaryStatement :
  String
tailBoundaryStatement =
  "This receipt is fail-closed: it records the geometric tail step only.  No analytic derivation, no KP promotion, no continuum Yang-Mills claim, and no Clay promotion are asserted."

record YMGeometricTailHalfBoundReceipt : Setω where
  field
    status :
      YMGeometricTailHalfBoundStatus

    statusIsCanonical :
      status ≡ geometricTailHalfBoundReceiptRecorded

    ratioSurface :
      YMGeometricTailRatioSurface

    ratioSurfaceIsCanonical :
      ratioSurface ≡ ratioBoundAtQuarterRecorded

    ratioUpperBoundNumerator :
      Nat

    ratioUpperBoundNumeratorIsOne :
      ratioUpperBoundNumerator ≡ quarterRatioNumerator

    ratioUpperBoundDenominator :
      Nat

    ratioUpperBoundDenominatorIsFour :
      ratioUpperBoundDenominator ≡ quarterRatioDenominator

    seriesShape :
      YMGeometricTailSeriesShape

    seriesShapeIsCanonical :
      seriesShape ≡ geometricSeriesTailStartsAtOneRecorded

    tailPowerShape :
      YMGeometricTailSeriesShape

    tailPowerShapeIsCanonical :
      tailPowerShape ≡ geometricSeriesTailUsesPowersOfRRecorded

    halfEnvelope :
      YMGeometricTailEnvelope

    halfEnvelopeIsCanonical :
      halfEnvelope ≡ tailEnvelopeAtMostHalfRecorded

    thirdEnvelope :
      YMGeometricTailEnvelope

    thirdEnvelopeIsCanonical :
      thirdEnvelope ≡ tailEnvelopeAtMostThirdRecorded

    tailHalfNumeratorField :
      Nat

    tailHalfNumeratorFieldIsOne :
      tailHalfNumeratorField ≡ tailHalfNumerator

    tailHalfDenominatorField :
      Nat

    tailHalfDenominatorFieldIsTwo :
      tailHalfDenominatorField ≡ tailHalfDenominator

    tailThirdNumeratorField :
      Nat

    tailThirdNumeratorFieldIsOne :
      tailThirdNumeratorField ≡ tailThirdNumerator

    tailThirdDenominatorField :
      Nat

    tailThirdDenominatorFieldIsThree :
      tailThirdDenominatorField ≡ tailThirdDenominator

    tailFormula :
      String

    tailFormulaIsCanonical :
      tailFormula ≡ "sum_{n>=1} r^n = r/(1-r)"

    tailShapeSummary :
      String

    tailShapeSummaryIsCanonical :
      tailShapeSummary ≡ tailShapeStatement

    dependencyInventory :
      List YMGeometricTailDependency

    dependencyInventoryIsCanonical :
      dependencyInventory ≡ canonicalYMGeometricTailDependencies

    nonClaims :
      List YMGeometricTailNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMGeometricTailNonClaims

    promotionFlags :
      List YMGeometricTailPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    promotionClosed :
      Bool

    promotionClosedIsFalse :
      promotionClosed ≡ false

    dependencyInventorySummary :
      String

    dependencyInventorySummaryIsCanonical :
      dependencyInventorySummary ≡
      "Dependencies: RA geometric-series authority surface; builtin Bool/Nat/String/equality; list ledger; fail-closed boundary."

    receiptBoundary :
      List String

open YMGeometricTailHalfBoundReceipt public

canonicalYMGeometricTailHalfBoundReceipt :
  YMGeometricTailHalfBoundReceipt
canonicalYMGeometricTailHalfBoundReceipt =
  record
    { status =
        geometricTailHalfBoundReceiptRecorded
    ; statusIsCanonical =
        refl
    ; ratioSurface =
        ratioBoundAtQuarterRecorded
    ; ratioSurfaceIsCanonical =
        refl
    ; ratioUpperBoundNumerator =
        1
    ; ratioUpperBoundNumeratorIsOne =
        refl
    ; ratioUpperBoundDenominator =
        4
    ; ratioUpperBoundDenominatorIsFour =
        refl
    ; seriesShape =
        geometricSeriesTailStartsAtOneRecorded
    ; seriesShapeIsCanonical =
        refl
    ; tailPowerShape =
        geometricSeriesTailUsesPowersOfRRecorded
    ; tailPowerShapeIsCanonical =
        refl
    ; halfEnvelope =
        tailEnvelopeAtMostHalfRecorded
    ; halfEnvelopeIsCanonical =
        refl
    ; thirdEnvelope =
        tailEnvelopeAtMostThirdRecorded
    ; thirdEnvelopeIsCanonical =
        refl
    ; tailHalfNumeratorField =
        1
    ; tailHalfNumeratorFieldIsOne =
        refl
    ; tailHalfDenominatorField =
        2
    ; tailHalfDenominatorFieldIsTwo =
        refl
    ; tailThirdNumeratorField =
        1
    ; tailThirdNumeratorFieldIsOne =
        refl
    ; tailThirdDenominatorField =
        3
    ; tailThirdDenominatorFieldIsThree =
        refl
    ; tailFormula =
        "sum_{n>=1} r^n = r/(1-r)"
    ; tailFormulaIsCanonical =
        refl
    ; tailShapeSummary =
        tailShapeStatement
    ; tailShapeSummaryIsCanonical =
        refl
    ; dependencyInventory =
        canonicalYMGeometricTailDependencies
    ; dependencyInventoryIsCanonical =
        refl
    ; nonClaims =
        canonicalYMGeometricTailNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; promotionClosed =
        false
    ; promotionClosedIsFalse =
        refl
    ; dependencyInventorySummary =
        "Dependencies: RA geometric-series authority surface; builtin Bool/Nat/String/equality; list ledger; fail-closed boundary."
    ; dependencyInventorySummaryIsCanonical =
        refl
    ; receiptBoundary =
        "r <= 1/4 is recorded as the scalar ratio hypothesis surface"
        ∷ "The geometric-series tail shape is recorded as sum_{n>=1} r^n = r/(1-r)"
        ∷ "The stronger 1/3 envelope is named alongside the <= 1/2 conclusion surface"
        ∷ "Dependencies are named locally: real-analysis authority surface, builtin equality/Bool/Nat/String, and the list ledger"
        ∷ "No analytic derivation, no KP promotion, no continuum Yang-Mills claim, and no Clay promotion are asserted"
        ∷ []
    }

geometricTailHalfBoundPromotionClosed :
  promotionClosed canonicalYMGeometricTailHalfBoundReceipt
  ≡
  false
geometricTailHalfBoundPromotionClosed =
  refl

