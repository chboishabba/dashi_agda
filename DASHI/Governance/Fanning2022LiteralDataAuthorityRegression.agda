module DASHI.Governance.Fanning2022LiteralDataAuthorityRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.Fanning2022SupplementaryDataAuthorityExact as Supplement
import DASHI.Governance.Fanning2022LiteralDataToFigureCommutationExact as Commutation

------------------------------------------------------------------------
-- Focused regression for the literal-data admission frontier.
------------------------------------------------------------------------

publishedBiophysicalCount :
  Supplement.SupplementaryDataScope.biophysicalIndicatorCount
    Supplement.publishedScope ≡ 6
publishedBiophysicalCount = refl

publishedSocialCount :
  Supplement.SupplementaryDataScope.socialIndicatorCount
    Supplement.publishedScope ≡ 11
publishedSocialCount = refl

publishedHistoricalWindow :
  Supplement.SupplementaryDataScope.historicalStart Supplement.publishedScope ≡ 1992
publishedHistoricalWindow = refl

publishedProjectionEnd :
  Supplement.SupplementaryDataScope.projectionEnd Supplement.publishedScope ≡ 2050
publishedProjectionEnd = refl

publishedProjectionCarriesLower66 :
  Supplement.SupplementaryDataScope.carriesLower66 Supplement.publishedScope ≡ true
publishedProjectionCarriesLower66 = refl

publishedProjectionCarriesMedian :
  Supplement.SupplementaryDataScope.carriesMedian Supplement.publishedScope ≡ true
publishedProjectionCarriesMedian = refl

publishedProjectionCarriesUpper66 :
  Supplement.SupplementaryDataScope.carriesUpper66 Supplement.publishedScope ≡ true
publishedProjectionCarriesUpper66 = refl

literalAdmissionStillRequiresRowReceipt :
  Commutation.FanningLiteralCommutationBoundary.thisModuleClaimsWorkbookAlreadyIngested
    Commutation.canonicalFanningLiteralCommutationBoundary ≡ false
literalAdmissionStillRequiresRowReceipt = refl

sourceLocatorAloneIsNotLiteralRow :
  Supplement.FanningSupplementaryDataBoundary.workbookLocatorIsLiteralRowReceipt
    Supplement.canonicalFanningSupplementaryDataBoundary ≡ false
sourceLocatorAloneIsNotLiteralRow = refl

record FanningLiteralDataRegressionBoundary : Set where
  constructor fanningLiteralDataRegressionBoundary
  field
    exactDatasetScopeRecorded : Bool
    exactDatasetScopeRecordedIsTrue : exactDatasetScopeRecorded ≡ true
    literalRowsAlreadyEmbedded : Bool
    literalRowsAlreadyEmbeddedIsFalse : literalRowsAlreadyEmbedded ≡ false
    syntheticRowsPromotedAsSourceRows : Bool
    syntheticRowsPromotedAsSourceRowsIsFalse : syntheticRowsPromotedAsSourceRows ≡ false

canonicalFanningLiteralDataRegressionBoundary : FanningLiteralDataRegressionBoundary
canonicalFanningLiteralDataRegressionBoundary =
  fanningLiteralDataRegressionBoundary true refl false refl false refl
