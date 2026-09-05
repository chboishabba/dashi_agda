module DASHI.Analysis.BishopRound11PowerSeriesLocalChartExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

------------------------------------------------------------------------
-- ROUND11 LOCAL POWER-SERIES CHART
--
-- Only proof-bearing coordinates are promoted here.  The older elementary
-- series record also contains several Set-valued descriptive fields; those are
-- deliberately NOT treated as evidence.  What Round11 genuinely supplies is:
--
--   * the literal elementary-series object;
--   * pointwise Bishop equivalences to concrete signed factorial-power terms;
--   * actual absolute-convergence receipts at every Bishop point.
------------------------------------------------------------------------

record Round11LocalPowerSeriesChart : Set₁ where
  field
    round11 : Round11.Round11BishopCutset

    dataSet : Elementary.BishopElementaryPowerSeriesData
    dataSetIsRound11 : dataSet ≡ Round11.elementarySeries round11

    concreteTerms : Terms.ConcreteSineCosineTermIdentification dataSet

    sineAbsolutelyConvergentAtEveryBishopPoint :
      (point : Bishop.Bishopℝ) →
      Bishop.BishopAbsoluteSeriesConvergent
        (Elementary.sineTerm dataSet point)

    cosineAbsolutelyConvergentAtEveryBishopPoint :
      (point : Bishop.Bishopℝ) →
      Bishop.BishopAbsoluteSeriesConvergent
        (Elementary.cosineTerm dataSet point)

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
  ; reading =
      "Round11 proof-bearing chart: literal sine/cosine terms are identified with concrete signed factorial powers and are absolutely convergent at every Bishop point."
  }

------------------------------------------------------------------------
-- The local chart does not itself cross foundations.  DLMF's theorem is stated
-- for the classical power-series derivative; the consumer uses the Bishop
-- division-free factor derivative.  Their relationship remains explicit.
------------------------------------------------------------------------

record ClassicalToBishopDerivativeSemanticBridge
    (chart : Round11LocalPowerSeriesChart) : Set₁ where
  field
    ClassicalPowerSeriesObject : Set
    classicalPowerSeriesObject : ClassicalPowerSeriesObject

    sourceCoefficientAndCentreIdentification : Set
    sourceCoefficientAndCentreIdentificationEvidence :
      sourceCoefficientAndCentreIdentification

    sourceInteriorDomainContainsRequestedPoints : Set
    sourceInteriorDomainContainsRequestedPointsEvidence :
      sourceInteriorDomainContainsRequestedPoints

    classicalTermwiseDerivativeMatchesLocalDerivedSeries : Set
    classicalTermwiseDerivativeMatchesLocalDerivedSeriesEvidence :
      classicalTermwiseDerivativeMatchesLocalDerivedSeries

    classicalDerivativeImpliesBishopFactorDerivative : Set
    classicalDerivativeImpliesBishopFactorDerivativeEvidence :
      classicalDerivativeImpliesBishopFactorDerivative

    reading : String

open ClassicalToBishopDerivativeSemanticBridge public

data LocalCoefficientChartAutomaticallyIdentifiesClassicalDerivative : Set where

localChartDoesNotCollapseDerivativeFoundations :
  LocalCoefficientChartAutomaticallyIdentifiesClassicalDerivative → ⊥
localChartDoesNotCollapseDerivativeFoundations ()

record Status : Set where
  field
    round11LiteralTermIdentificationOwned : Bool
    globalBishopAbsoluteConvergenceOwned : Bool
    descriptiveSetFieldsNotPromotedToEvidence : Bool
    crossFoundationDerivativeBridgeClosed : Bool

    round11LiteralTermIdentificationOwnedIsTrue :
      round11LiteralTermIdentificationOwned ≡ true
    globalBishopAbsoluteConvergenceOwnedIsTrue :
      globalBishopAbsoluteConvergenceOwned ≡ true
    descriptiveSetFieldsNotPromotedToEvidenceIsTrue :
      descriptiveSetFieldsNotPromotedToEvidence ≡ true
    crossFoundationDerivativeBridgeClosedIsFalse :
      crossFoundationDerivativeBridgeClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { round11LiteralTermIdentificationOwned = true
  ; globalBishopAbsoluteConvergenceOwned = true
  ; descriptiveSetFieldsNotPromotedToEvidence = true
  ; crossFoundationDerivativeBridgeClosed = false
  ; round11LiteralTermIdentificationOwnedIsTrue = refl
  ; globalBishopAbsoluteConvergenceOwnedIsTrue = refl
  ; descriptiveSetFieldsNotPromotedToEvidenceIsTrue = refl
  ; crossFoundationDerivativeBridgeClosedIsFalse = refl
  }
