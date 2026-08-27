module DASHI.Governance.Fanning2022SupplementaryDataAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.SafeJustSourceRegistryExact as Sources
import DASHI.Governance.Fanning2022DataRealizationExact as Data

------------------------------------------------------------------------
-- FANNING ET AL. 2022: SUPPLEMENTARY-DATA AUTHORITY CONTRACT
--
-- PRIMARY EMPIRICAL SOURCE
--
-- Andrew L. Fanning, Daniel W. O'Neill, Jason Hickel & Nicolas Roux,
-- "The social shortfall and ecological overshoot of nations",
-- Nature Sustainability 5 (2022), 26--36,
-- DOI 10.1038/s41893-021-00799-z.
--
-- SOURCE-PUBLISHED DATA SURFACES
--
-- Nature article data availability:
--   the country-level data produced in the analysis are included in the
--   Supplementary Information and exposed through goodlife.leeds.ac.uk.
--
-- White Rose accepted supplementary spreadsheet filename:
--   Fanning et al_2021-SupplementaryData_Social shortfall and ecological
--   overshoot_authorAccepted.xlsx
--
-- University of Leeds public national-trends download:
--   SocialShortfallAndEcologicalOvershoot_SupplementaryData.xlsx
--
-- The publisher description states that the spreadsheet contains the six
-- biophysical and eleven social indicator country-level data, historical
-- observations (1992--2015), and BAU projections (2016--2050) with 66% upper
-- and lower intervals.
--
-- IMPORTANT
-- This module records the admission contract for literal rows.  It does not
-- pretend that naming the workbook reconstructs any workbook value.  A row is
-- literal only when an ingestion step supplies a source-row receipt.
------------------------------------------------------------------------

data SupplementaryDataSurface : Set where
  natureSupplementaryData
  whiteRoseAcceptedSpreadsheet
  leedsNationalTrendsDownload
  : SupplementaryDataSurface

record SupplementaryDataReference : Set where
  constructor supplementaryDataReference
  field
    surface : SupplementaryDataSurface
    locator : String
    sourceDOI : String
    boundedRole : String

open SupplementaryDataReference public

natureDataReference : SupplementaryDataReference
natureDataReference = supplementaryDataReference
  natureSupplementaryData
  "https://www.nature.com/articles/s41893-021-00799-z#Sec20"
  "10.1038/s41893-021-00799-z"
  "publisher data-availability and Supplementary Data authority; does not by itself reconstruct spreadsheet rows"

whiteRoseDataReference : SupplementaryDataReference
whiteRoseDataReference = supplementaryDataReference
  whiteRoseAcceptedSpreadsheet
  "https://eprints.whiterose.ac.uk/id/eprint/180834/13/Fanning%20et%20al_2021-SupplementaryData_Social%20shortfall%20and%20ecological%20overshoot_authorAccepted.xlsx"
  "10.1038/s41893-021-00799-z"
  "accepted supplementary spreadsheet mirror; row-level values require literal ingestion"

leedsDataReference : SupplementaryDataReference
leedsDataReference = supplementaryDataReference
  leedsNationalTrendsDownload
  "https://goodlife.leeds.ac.uk/wp-content/uploads/sites/20/2021/11/SocialShortfallAndEcologicalOvershoot_SupplementaryData.xlsx"
  "10.1038/s41893-021-00799-z"
  "University of Leeds national-trends dataset download for the published analysis"

source : Sources.SourceReference
source = Sources.fanning2022

------------------------------------------------------------------------
-- Literal-row admission.
--
-- A datum becomes admitted as literal empirical data only when the ingestion
-- layer supplies both a source surface and a row locator/receipt.  There is no
-- constructor from an arbitrary CountryYearDatum alone.
------------------------------------------------------------------------

record SourceRowLocator : Set where
  constructor sourceRowLocator
  field
    sheetCode : Nat
    rowCode : Nat
    columnCode : Nat

record LiteralSourceRow (datum : Data.CountryYearDatum) : Set where
  constructor literalSourceRow
  field
    dataReference : SupplementaryDataReference
    rowLocator : SourceRowLocator
    sourceValuePreserved : Bool
    sourceValuePreservedIsTrue : sourceValuePreserved ≡ true
    datumAuthorityPreserved : Bool
    datumAuthorityPreservedIsTrue : datumAuthorityPreserved ≡ true

-- Synthetic/local values cannot become literal merely through the datum type.
data SyntheticWitness : Data.CountryYearDatum → Set where
  syntheticWitness : (d : Data.CountryYearDatum) → SyntheticWitness d

syntheticWitnessIsNotLiteralReceipt :
  {d : Data.CountryYearDatum} →
  SyntheticWitness d → LiteralSourceRow d → Set
syntheticWitnessIsNotLiteralReceipt _ _ = ⊤

record SupplementaryDataScope : Set where
  constructor supplementaryDataScope
  field
    biophysicalIndicatorCount : Nat
    socialIndicatorCount : Nat
    historicalStart : Nat
    historicalEnd : Nat
    projectionStart : Nat
    projectionEnd : Nat
    carriesLower66 : Bool
    carriesMedian : Bool
    carriesUpper66 : Bool

publishedScope : SupplementaryDataScope
publishedScope = supplementaryDataScope 6 11 1992 2015 2016 2050 true true true

record FanningSupplementaryDataBoundary : Set where
  constructor fanningSupplementaryDataBoundary
  field
    workbookLocatorIsLiteralRowReceipt : Bool
    workbookLocatorIsLiteralRowReceiptIsFalse : workbookLocatorIsLiteralRowReceipt ≡ false
    arbitraryDatumIsLiteralWorkbookDatum : Bool
    arbitraryDatumIsLiteralWorkbookDatumIsFalse : arbitraryDatumIsLiteralWorkbookDatum ≡ false
    rowReceiptMustPreserveAuthority : Bool
    rowReceiptMustPreserveAuthorityIsTrue : rowReceiptMustPreserveAuthority ≡ true
    datasetHasSixBiophysicalIndicators : Bool
    datasetHasSixBiophysicalIndicatorsIsTrue : datasetHasSixBiophysicalIndicators ≡ true
    datasetHasElevenSocialIndicators : Bool
    datasetHasElevenSocialIndicatorsIsTrue : datasetHasElevenSocialIndicators ≡ true
    sourceCitationAuthorsIngestionTheorems : Bool
    sourceCitationAuthorsIngestionTheoremsIsFalse : sourceCitationAuthorsIngestionTheorems ≡ false

canonicalFanningSupplementaryDataBoundary : FanningSupplementaryDataBoundary
canonicalFanningSupplementaryDataBoundary =
  fanningSupplementaryDataBoundary
    false refl false refl true refl true refl true refl false refl
