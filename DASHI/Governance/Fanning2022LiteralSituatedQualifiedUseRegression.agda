module DASHI.Governance.Fanning2022LiteralSituatedQualifiedUseRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.Fanning2022DataRealizationExact as Data
import DASHI.Governance.Fanning2022SupplementaryDataAuthorityExact as Supplement
import DASHI.Governance.Fanning2022LiteralDataToFigureCommutationExact as Figure
import DASHI.Governance.Fanning2022LiteralSituatedQualifiedUseBridgeExact as Bridge

------------------------------------------------------------------------
-- Focused regression for the literal-data / situated-authority weld.
--
-- No empirical row is manufactured here.  All receipts are universally
-- quantified over a row already admitted by LiteralSourceRow.
------------------------------------------------------------------------

projectionRowCanBeQualifiedWithoutLosingSource :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  Bridge.BAUProjectionDatum datum →
  Figure.FigureCommutationAdmission datum literal →
  Bridge.LiteralSituatedQualifiedResearchUse datum literal
projectionRowCanBeQualifiedWithoutLosingSource = Bridge.attachSituatedResearchUse

qualifiedRowStillReturnsOriginalLiteralReceipt :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  (receipt : Bridge.LiteralSituatedQualifiedResearchUse datum literal) →
  Bridge.literalSourceSurvivesQualifiedResearchUse receipt ≡ literal
qualifiedRowStillReturnsOriginalLiteralReceipt = Bridge.literalSourceIsOriginalInput

historicalObservationCannotEnterBAUProjectionGate :
  {datum : Data.CountryYearDatum} →
  Data.CountryYearDatum.authority datum ≡ Data.observedDatum →
  Bridge.BAUProjectionDatum datum → ⊥
historicalObservationCannotEnterBAUProjectionGate = Bridge.observedDatumIsNotBAUProjection

boundaryKeepsLiteralProvenance :
  Bridge.LiteralSituatedAuthorityBoundary.literalSourceReceiptSurvivesSituatedQualification
    Bridge.canonicalLiteralSituatedAuthorityBoundary ≡ true
boundaryKeepsLiteralProvenance = refl

boundaryBlocksHistoricalForecastPromotion :
  Bridge.LiteralSituatedAuthorityBoundary.historicalObservationCanSilentlyBecomeBAUForecastEvidence
    Bridge.canonicalLiteralSituatedAuthorityBoundary ≡ false
boundaryBlocksHistoricalForecastPromotion = refl

boundaryBlocksCausalPromotion :
  Bridge.LiteralSituatedAuthorityBoundary.qualifiedLiteralResearchUseCreatesCausalAuthority
    Bridge.canonicalLiteralSituatedAuthorityBoundary ≡ false
boundaryBlocksCausalPromotion = refl

boundaryBlocksDecisionPromotion :
  Bridge.LiteralSituatedAuthorityBoundary.qualifiedLiteralResearchUseCreatesDecisionAuthority
    Bridge.canonicalLiteralSituatedAuthorityBoundary ≡ false
boundaryBlocksDecisionPromotion = refl

boundaryDoesNotClaimWorkbookIngestion :
  Bridge.LiteralSituatedAuthorityBoundary.thisModuleClaimsWorkbookAlreadyIngested
    Bridge.canonicalLiteralSituatedAuthorityBoundary ≡ false
boundaryDoesNotClaimWorkbookIngestion = refl
