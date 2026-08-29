module DASHI.Governance.Fanning2022LiteralSituatedQualifiedUseBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.SituatedClaimAuthoritySystemExact as Situated
import DASHI.Governance.Fanning2022DataRealizationExact as Data
import DASHI.Governance.Fanning2022SupplementaryDataAuthorityExact as Supplement
import DASHI.Governance.Fanning2022LiteralDataToFigureCommutationExact as Figure
import DASHI.Governance.SafeJustSituatedClaimAuthorityBridgeExact as Authority

------------------------------------------------------------------------
-- FANNING 2022: LITERAL DATA -> SITUATED QUALIFIED RESEARCH USE
--
-- Andrew L. Fanning, Daniel W. O'Neill, Jason Hickel & Nicolas Roux,
-- "The social shortfall and ecological overshoot of nations",
-- Nature Sustainability 5 (2022), 26--36,
-- DOI 10.1038/s41893-021-00799-z.
--
-- This module is a DASHI cross-pollination adapter.  It does not ingest the
-- workbook and does not invent a datum.  Instead it states the exact endpoint
-- available once an external ingestion step supplies a LiteralSourceRow and a
-- proved data-to-figure commuting receipt.
--
-- The important extra gate is datum authority: only a row whose authority is
-- one of the published BAU projection bands may be attached to the existing
-- Fanning BAU forecast research-use qualification.  An observed historical row
-- cannot silently become forecast evidence merely because it is literal.
------------------------------------------------------------------------

data BAUProjectionDatum (datum : Data.CountryYearDatum) : Set where
  medianProjectionDatum :
    Data.CountryYearDatum.authority datum ≡ Data.projectedMedian →
    BAUProjectionDatum datum
  lower66ProjectionDatum :
    Data.CountryYearDatum.authority datum ≡ Data.projectedLower66 →
    BAUProjectionDatum datum
  upper66ProjectionDatum :
    Data.CountryYearDatum.authority datum ≡ Data.projectedUpper66 →
    BAUProjectionDatum datum

observedDatumIsNotBAUProjection :
  {datum : Data.CountryYearDatum} →
  Data.CountryYearDatum.authority datum ≡ Data.observedDatum →
  BAUProjectionDatum datum → ⊥
observedDatumIsNotBAUProjection observed (medianProjectionDatum projected) with
  trans (sym observed) projected
... | ()
observedDatumIsNotBAUProjection observed (lower66ProjectionDatum projected) with
  trans (sym observed) projected
... | ()
observedDatumIsNotBAUProjection observed (upper66ProjectionDatum projected) with
  trans (sym observed) projected
... | ()

------------------------------------------------------------------------
-- End-to-end receipt.
--
-- The record is indexed by the exact literal row.  The same literal proof
-- object survives the figure transformation and remains exposed after the
-- situated QualifiedUse is attached.  The qualified-use field is the existing
-- #625 authority product; no second authority calculus is introduced here.
------------------------------------------------------------------------

record LiteralSituatedQualifiedResearchUse
  (datum : Data.CountryYearDatum)
  (literal : Supplement.LiteralSourceRow datum) : Set where
  constructor literalSituatedQualifiedResearchUse
  field
    projectionDatum : BAUProjectionDatum datum
    figureAdmission : Figure.FigureCommutationAdmission datum literal
    situatedResearchUse :
      Situated.QualifiedUse
        Authority.safeJustSituatedClaimAuthoritySystem
        Authority.safeJustResearchAgenda
        Authority.safeJustIndicatorCategory
        Authority.fanningBAUProjectionClaim
        Authority.repositorySourceRegistryContext
        Authority.forecastResearchConsumer
        Authority.researchSynthesisUse
        Authority.attributionAndResidualCarriage
    literalSourceReceipt : Supplement.LiteralSourceRow datum
    literalSourceReceiptIsInput : literalSourceReceipt ≡ literal

attachSituatedResearchUse :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  BAUProjectionDatum datum →
  Figure.FigureCommutationAdmission datum literal →
  LiteralSituatedQualifiedResearchUse datum literal
attachSituatedResearchUse {literal = literal} projection admission =
  literalSituatedQualifiedResearchUse
    projection
    admission
    Authority.fanningQualifiedResearchUse
    literal
    refl

literalSourceSurvivesQualifiedResearchUse :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  LiteralSituatedQualifiedResearchUse datum literal →
  Supplement.LiteralSourceRow datum
literalSourceSurvivesQualifiedResearchUse receipt =
  LiteralSituatedQualifiedResearchUse.literalSourceReceipt receipt

literalSourceIsOriginalInput :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  (receipt : LiteralSituatedQualifiedResearchUse datum literal) →
  literalSourceSurvivesQualifiedResearchUse receipt ≡ literal
literalSourceIsOriginalInput receipt =
  LiteralSituatedQualifiedResearchUse.literalSourceReceiptIsInput receipt

------------------------------------------------------------------------
-- The richer end-to-end receipt still does not open stronger consumers.
------------------------------------------------------------------------

literalResearchUseDoesNotCreateCausalQualification :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  LiteralSituatedQualifiedResearchUse datum literal →
  Situated.QualifiedUse
    Authority.safeJustSituatedClaimAuthoritySystem
    Authority.safeJustResearchAgenda
    Authority.safeJustIndicatorCategory
    Authority.fanningBAUProjectionClaim
    Authority.repositorySourceRegistryContext
    Authority.causalMechanismConsumer
    Authority.causalPromotionUse
    Authority.attributionAndResidualCarriage → ⊥
literalResearchUseDoesNotCreateCausalQualification _ =
  Authority.fanningCausalQualifiedUseImpossible

literalResearchUseDoesNotCreateDecisionAuthority :
  {datum : Data.CountryYearDatum} →
  {literal : Supplement.LiteralSourceRow datum} →
  LiteralSituatedQualifiedResearchUse datum literal →
  Authority.DecisionAuthorized
    Authority.repositorySourceRegistryContext
    Authority.fanningBAUProjectionClaim
    Authority.policyInterventionUse → ⊥
literalResearchUseDoesNotCreateDecisionAuthority _ =
  Authority.fanningResearchUseDoesNotCreateDecisionAuthority

record LiteralSituatedAuthorityBoundary : Set where
  constructor literalSituatedAuthorityBoundary
  field
    literalSourceReceiptSurvivesSituatedQualification : Bool
    literalSourceReceiptSurvivesSituatedQualificationIsTrue :
      literalSourceReceiptSurvivesSituatedQualification ≡ true
    historicalObservationCanSilentlyBecomeBAUForecastEvidence : Bool
    historicalObservationCanSilentlyBecomeBAUForecastEvidenceIsFalse :
      historicalObservationCanSilentlyBecomeBAUForecastEvidence ≡ false
    qualifiedLiteralResearchUseCreatesCausalAuthority : Bool
    qualifiedLiteralResearchUseCreatesCausalAuthorityIsFalse :
      qualifiedLiteralResearchUseCreatesCausalAuthority ≡ false
    qualifiedLiteralResearchUseCreatesDecisionAuthority : Bool
    qualifiedLiteralResearchUseCreatesDecisionAuthorityIsFalse :
      qualifiedLiteralResearchUseCreatesDecisionAuthority ≡ false
    thisModuleClaimsWorkbookAlreadyIngested : Bool
    thisModuleClaimsWorkbookAlreadyIngestedIsFalse :
      thisModuleClaimsWorkbookAlreadyIngested ≡ false

canonicalLiteralSituatedAuthorityBoundary : LiteralSituatedAuthorityBoundary
canonicalLiteralSituatedAuthorityBoundary =
  literalSituatedAuthorityBoundary true refl false refl false refl false refl false refl
