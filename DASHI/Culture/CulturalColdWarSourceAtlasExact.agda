module DASHI.Culture.CulturalColdWarSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE ATLAS
--
-- These entries record bounded external-source claims only.  A citation does
-- not import proof, causal force, authority, or a DASHI theorem.  Historical
-- fixture constructors consuming these entries remain explicit below the atlas.
------------------------------------------------------------------------

data SourceRole : Set where
  institutionalHistoryRole
  archivalExhibitionRole
  intelligenceHistoryRole
  : SourceRole

record HistoricalSourceClaim : Set where
  constructor historical-source-claim
  field
    sourceName : String
    sourceLocator : String
    sourceRole : SourceRole
    boundedClaim : String
    citationImportsProof : Bool
    citationImportsAuthority : Bool
    citationImportsCausalPromotion : Bool

open HistoricalSourceClaim public

ciaCCFSource : HistoricalSourceClaim
ciaCCFSource =
  historical-source-claim
    "Michael S. Warner, CIA Center for the Study of Intelligence"
    "Origins of the Congress for Cultural Freedom, 1949-1950"
    intelligenceHistoryRole
    "The Congress for Cultural Freedom was a CIA covert operation; covert funding supported its formation and activity."
    false false false

momaInternationalProgramFundingSource : HistoricalSourceClaim
momaInternationalProgramFundingSource =
  historical-source-claim
    "Museum of Modern Art Archives"
    "International Council and International Program Records, Subseries I.A"
    institutionalHistoryRole
    "A five-year Rockefeller Brothers Fund grant secured in July 1952 funded development of MoMA's International Program; the International Council later assumed sponsorship."
    false false false

newAmericanPaintingSource : HistoricalSourceClaim
newAmericanPaintingSource =
  historical-source-claim
    "Museum of Modern Art"
    "The New American Painting as Shown in Eight European Countries 1958-1959"
    archivalExhibitionRole
    "The exhibition was organized by the International Program of the Museum of Modern Art and presented seventeen American artists across the documented European tour and New York presentation."
    false false false

momaAbExInternationalProgramSource : HistoricalSourceClaim
momaAbExInternationalProgramSource =
  historical-source-claim
    "Museum of Modern Art, International Program history"
    "MoMA and the World: The International Program"
    institutionalHistoryRole
    "MoMA describes many Abstract Expressionist artists as having been shown abroad by the International Program in the 1950s."
    false false false

record CulturalColdWarSourceAtlasBoundary : Set where
  constructor cultural-cold-war-source-atlas-boundary
  field
    ciaCCFClaimRecorded : Bool
    rockefellerInternationalProgramClaimRecorded : Bool
    newAmericanPaintingOrganisationRecorded : Bool
    abstractExpressionistInternationalCirculationRecorded : Bool
    citationsImportProof : Bool
    citationsImportAuthority : Bool
    citationsImportCausalPromotion : Bool

canonicalCulturalColdWarSourceAtlasBoundary : CulturalColdWarSourceAtlasBoundary
canonicalCulturalColdWarSourceAtlasBoundary =
  cultural-cold-war-source-atlas-boundary true true true true false false false
