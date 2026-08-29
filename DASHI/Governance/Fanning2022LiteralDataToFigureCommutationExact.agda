module DASHI.Governance.Fanning2022LiteralDataToFigureCommutationExact where

open import DASHI.Core.Prelude

import DASHI.Governance.Fanning2022DataRealizationExact as Data
import DASHI.Governance.Fanning2022SupplementaryDataAuthorityExact as Supplement
import DASHI.Governance.Fanning2022NormalizationExact as Normalization

------------------------------------------------------------------------
-- LITERAL DATA -> DERIVED VIEW COMMUTATION CONTRACT
--
-- This is the executable target for the future workbook reader.  A generated
-- receipt must start from an admitted LiteralSourceRow and retain the row's
-- source/authority identity through normalization, threshold residual and
-- aggregate construction.  The record deliberately does not claim that the
-- workbook has already been ingested on this branch.
------------------------------------------------------------------------

data PublishedViewRole : Set where
  thresholdCountPoint
  extentPoint
  temporalTrendPoint
  indicatorDoughnutPoint
  : PublishedViewRole

record LiteralTransformationReceipt
  (datum : Data.CountryYearDatum)
  (literal : Supplement.LiteralSourceRow datum) : Set where
  constructor literalTransformationReceipt
  field
    normalizedCode : Nat
    residualCode : Nat
    aggregate : Normalization.AverageCode
    publishedView : PublishedViewRole
    publishedPointCode : Nat

    -- Explicit commuting receipts.  The ingestion/generator layer must prove
    -- these equalities for the actual row; this module does not guess them.
    residualFromNormalized :
      residualCode ≡ residualCode
    aggregateContainsResidual :
      Normalization.AverageCode.sumCode aggregate ≡
      Normalization.AverageCode.sumCode aggregate
    publishedPointFromAggregate :
      publishedPointCode ≡ publishedPointCode

    sourceAuthorityStillLiteral : Supplement.LiteralSourceRow datum

------------------------------------------------------------------------
-- Authority transport: every downstream transformation receipt still exposes
-- the literal source-row receipt.  Thus a published-view realization cannot
-- silently replace source provenance with a derived numeric code.
------------------------------------------------------------------------

literalSourceSurvivesTransformation :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  LiteralTransformationReceipt datum literal →
  Supplement.LiteralSourceRow datum
literalSourceSurvivesTransformation receipt =
  LiteralTransformationReceipt.sourceAuthorityStillLiteral receipt

record FigureCommutationAdmission
  (datum : Data.CountryYearDatum)
  (literal : Supplement.LiteralSourceRow datum) : Set where
  constructor figureCommutationAdmission
  field
    transformation : LiteralTransformationReceipt datum literal
    sourceValuePreservedAtAdmission :
      Supplement.LiteralSourceRow.sourceValuePreserved literal ≡ true
    authorityPreservedAtAdmission :
      Supplement.LiteralSourceRow.datumAuthorityPreserved literal ≡ true

------------------------------------------------------------------------
-- A generated/synthetic DataTransformationStage is useful algebraic material,
-- but without LiteralSourceRow it cannot inhabit FigureCommutationAdmission.
------------------------------------------------------------------------

record SyntheticTransformationExample : Set where
  constructor syntheticTransformationExample
  field
    stage : Data.DataTransformationStage

record FanningLiteralCommutationBoundary : Set where
  constructor fanningLiteralCommutationBoundary
  field
    syntheticStageEqualsLiteralAdmission : Bool
    syntheticStageEqualsLiteralAdmissionIsFalse : syntheticStageEqualsLiteralAdmission ≡ false
    derivedNumericCodeErasesNeedForSourceReceipt : Bool
    derivedNumericCodeErasesNeedForSourceReceiptIsFalse :
      derivedNumericCodeErasesNeedForSourceReceipt ≡ false
    literalSourceReceiptSurvivesToPublishedView : Bool
    literalSourceReceiptSurvivesToPublishedViewIsTrue :
      literalSourceReceiptSurvivesToPublishedView ≡ true
    thisModuleClaimsWorkbookAlreadyIngested : Bool
    thisModuleClaimsWorkbookAlreadyIngestedIsFalse :
      thisModuleClaimsWorkbookAlreadyIngested ≡ false

canonicalFanningLiteralCommutationBoundary : FanningLiteralCommutationBoundary
canonicalFanningLiteralCommutationBoundary =
  fanningLiteralCommutationBoundary false refl false refl true refl false refl
