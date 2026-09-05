module DASHI.Analysis.BishopRound11PowerSeriesLocalChartExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

------------------------------------------------------------------------
-- ROUND11 LOCAL POWER-SERIES CHART
--
-- Before using any external termwise-differentiation theorem, record which
-- coordinates of the intended power series are already owned internally.
-- Round11 supplies the elementary-series data and a literal identification of
-- its sine/cosine terms with the signed factorial-power terms.
------------------------------------------------------------------------

record Round11LocalPowerSeriesChart : Set₁ where
  field
    round11 : Round11.Round11BishopCutset

    dataSet : Elementary.BishopElementaryPowerSeriesData
    dataSetIsRound11 : dataSet ≡ Round11.elementarySeries round11

    concreteTerms : Terms.ConcreteSineCosineTermIdentification dataSet

    sineAbsolutelyConvergentAtEveryBishopPoint :
      (point : Elementary.Bishop.Bishopℝ) →
      Elementary.Bishop.BishopAbsoluteSeriesConvergent
        (Elementary.sineTerm dataSet point)

    cosineAbsolutelyConvergentAtEveryBishopPoint :
      (point : Elementary.Bishop.Bishopℝ) →
      Elementary.Bishop.BishopAbsoluteSeriesConvergent
        (Elementary.cosineTerm dataSet point)

    sineOddFactorialCoordinateOwned : Set
    cosineEvenFactorialCoordinateOwned : Set
    alternatingSignCoordinateOwned : Set
    centreIsZeroCoordinateOwned : Set

    reading : String

open Round11LocalPowerSeriesChart public

canonicalRound11LocalPowerSeriesChart :
  (cutset : Round11.Round11BishopCutset) →
  Round11LocalPowerSeriesChart
canonicalRound11LocalPowerSeriesChart cutset = record
  { round11 = cutset
  ; dataSet = Round11.elementarySeries cutset
  ; dataSetIsRound11 = refl
  ; concreteTerms = Round11.round11ConcreteTermIdentification cutset
  ; sineAbsolutelyConvergentAtEveryBishopPoint =
      Elementary.sineAbsoluteConvergence (Round11.elementarySeries cutset)
  ; cosineAbsolutelyConvergentAtEveryBishopPoint =
      Elementary.cosineAbsoluteConvergence (Round11.elementarySeries cutset)
  ; sineOddFactorialCoordinateOwned = ⊤
  ; cosineEvenFactorialCoordinateOwned = ⊤
  ; alternatingSignCoordinateOwned = ⊤
  ; centreIsZeroCoordinateOwned = ⊤
  ; reading =
      "Round11 already owns the literal Bishop sine/cosine term families, absolute convergence, and their signed factorial-power chart."
  }

------------------------------------------------------------------------
-- The local chart does not itself cross from the classical DLMF derivative
-- semantics to the Bishop factor derivative.  That remains a separate bridge.
------------------------------------------------------------------------

record ClassicalToBishopDerivativeSemanticBridge
    (chart : Round11LocalPowerSeriesChart) : Set₁ where
  field
    classicalPowerSeriesObjectMatchesLocalChart : Set
    classicalInteriorDomainCoversLocalEvaluation : Set
    classicalTermwiseDerivativeMatchesLocalDerivedSeries : Set
    classicalDerivativeImpliesBishopFactorDerivative : Set
    reading : String

open ClassicalToBishopDerivativeSemanticBridge public

data LocalCoefficientChartAutomaticallyIdentifiesClassicalDerivative : Set where

localChartDoesNotCollapseDerivativeFoundations :
  LocalCoefficientChartAutomaticallyIdentifiesClassicalDerivative → ⊥
localChartDoesNotCollapseDerivativeFoundations ()

record Status : Set where
  field
    round11LocalSeriesChartOwned : Bool
    globalBishopAbsoluteConvergenceOwned : Bool
    coefficientAndIndexChartOwned : Bool
    crossFoundationDerivativeBridgeClosed : Bool

    round11LocalSeriesChartOwnedIsTrue : round11LocalSeriesChartOwned ≡ true
    globalBishopAbsoluteConvergenceOwnedIsTrue : globalBishopAbsoluteConvergenceOwned ≡ true
    coefficientAndIndexChartOwnedIsTrue : coefficientAndIndexChartOwned ≡ true
    crossFoundationDerivativeBridgeClosedIsFalse : crossFoundationDerivativeBridgeClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { round11LocalSeriesChartOwned = true
  ; globalBishopAbsoluteConvergenceOwned = true
  ; coefficientAndIndexChartOwned = true
  ; crossFoundationDerivativeBridgeClosed = false
  ; round11LocalSeriesChartOwnedIsTrue = refl
  ; globalBishopAbsoluteConvergenceOwnedIsTrue = refl
  ; coefficientAndIndexChartOwnedIsTrue = refl
  ; crossFoundationDerivativeBridgeClosedIsFalse = refl
  }
