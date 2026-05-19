module DASHI.Physics.Closure.HEPDataRatioTableArtifactReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataRatioTableArtifactRequest as R24

------------------------------------------------------------------------
-- HEP-R28: checksum-bound t43/t44 ratio artifact receipt.
--
-- This module records the successful name-based HEPData acquisition route for
-- the selected t43/t44 dimensionless phistar ratio lane.  It binds the local
-- artifact paths and SHA-256 digests.  It does not parse the CSVs, run a
-- DASHI projection, construct predictionFixedAt, construct a comparison law,
-- or promote W3/W4/W5/W8.

data HEPDataRatioTableArtifactReceiptStatus : Set where
  checksumBoundT43T44ArtifactsAcquiredNoProjection :
    HEPDataRatioTableArtifactReceiptStatus

data HEPDataRatioTableArtifactReceiptRole : Set where
  ratioValueTableT43 :
    HEPDataRatioTableArtifactReceiptRole
  ratioCovarianceTableT44 :
    HEPDataRatioTableArtifactReceiptRole

data HEPDataRatioTableArtifactAcquisitionRoute : Set where
  nameBasedHEPDataDownloadEndpoint :
    HEPDataRatioTableArtifactAcquisitionRoute

data HEPDataRatioTableArtifactRejectedRoute : Set where
  shortT43EndpointReturnedHEPDataErrorHTML :
    HEPDataRatioTableArtifactRejectedRoute
  shortT44EndpointReturnedHEPDataErrorHTML :
    HEPDataRatioTableArtifactRejectedRoute
  table43EndpointReturnedHEPDataErrorHTML :
    HEPDataRatioTableArtifactRejectedRoute

canonicalHEPDataRatioTableArtifactRejectedRoutes :
  List HEPDataRatioTableArtifactRejectedRoute
canonicalHEPDataRatioTableArtifactRejectedRoutes =
  shortT43EndpointReturnedHEPDataErrorHTML
  ∷ shortT44EndpointReturnedHEPDataErrorHTML
  ∷ table43EndpointReturnedHEPDataErrorHTML
  ∷ []

record HEPDataRatioTableArtifactChecksumEntry : Set where
  field
    role :
      HEPDataRatioTableArtifactReceiptRole

    tableDOI :
      String

    tableName :
      String

    acquisitionRoute :
      HEPDataRatioTableArtifactAcquisitionRoute

    acquisitionURL :
      String

    localPath :
      String

    sha256 :
      String

    firstHeaderLine :
      String

canonicalT43RatioArtifactChecksumEntry :
  HEPDataRatioTableArtifactChecksumEntry
canonicalT43RatioArtifactChecksumEntry =
  record
    { role =
        ratioValueTableT43
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t43"
    ; tableName =
        "phistar mass 50-76 over mass 76-106"
    ; acquisitionRoute =
        nameBasedHEPDataDownloadEndpoint
    ; acquisitionURL =
        "https://www.hepdata.net/download/table/ins2079374/phistar%20mass%2050-76%20over%20mass%2076-106/csv"
    ; localPath =
        "scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv"
    ; sha256 =
        "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"
    ; firstHeaderLine =
        "#: table_doi: 10.17182/hepdata.115656.v1/t43"
    }

canonicalT44RatioCovarianceArtifactChecksumEntry :
  HEPDataRatioTableArtifactChecksumEntry
canonicalT44RatioCovarianceArtifactChecksumEntry =
  record
    { role =
        ratioCovarianceTableT44
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t44"
    ; tableName =
        "Covariance matrices for phistar mass 50-76 over mass 76-106"
    ; acquisitionRoute =
        nameBasedHEPDataDownloadEndpoint
    ; acquisitionURL =
        "https://www.hepdata.net/download/table/ins2079374/Covariance%20matrices%20for%20phistar%20mass%2050-76%20over%20mass%2076-106/csv"
    ; localPath =
        "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv"
    ; sha256 =
        "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"
    ; firstHeaderLine =
        "#: table_doi: 10.17182/hepdata.115656.v1/t44"
    }

canonicalHEPDataRatioTableArtifactChecksumEntries :
  List HEPDataRatioTableArtifactChecksumEntry
canonicalHEPDataRatioTableArtifactChecksumEntries =
  canonicalT43RatioArtifactChecksumEntry
  ∷ canonicalT44RatioCovarianceArtifactChecksumEntry
  ∷ []

data HEPDataRatioTableArtifactReceiptBoundary : Set where
  noCSVParsingHere :
    HEPDataRatioTableArtifactReceiptBoundary
  noPredictionFixedAtHere :
    HEPDataRatioTableArtifactReceiptBoundary
  noProjectionRunHere :
    HEPDataRatioTableArtifactReceiptBoundary
  noComparisonLawHere :
    HEPDataRatioTableArtifactReceiptBoundary
  noW3W4W5W8PromotionHere :
    HEPDataRatioTableArtifactReceiptBoundary

canonicalHEPDataRatioTableArtifactReceiptBoundaries :
  List HEPDataRatioTableArtifactReceiptBoundary
canonicalHEPDataRatioTableArtifactReceiptBoundaries =
  noCSVParsingHere
  ∷ noPredictionFixedAtHere
  ∷ noProjectionRunHere
  ∷ noComparisonLawHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataRatioTableArtifactPromotionReceipt : Set where

ratioTableArtifactPromotionImpossibleHere :
  HEPDataRatioTableArtifactPromotionReceipt →
  ⊥
ratioTableArtifactPromotionImpossibleHere ()

record HEPDataRatioTableArtifactReceipt : Setω where
  field
    status :
      HEPDataRatioTableArtifactReceiptStatus

    priorRequest :
      R24.HEPDataRatioTableArtifactRequest

    checksumEntries :
      List HEPDataRatioTableArtifactChecksumEntry

    checksumEntriesAreCanonical :
      checksumEntries
      ≡
      canonicalHEPDataRatioTableArtifactChecksumEntries

    t43Sha256 :
      String

    t43Sha256IsCanonical :
      t43Sha256
      ≡
      "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"

    t44Sha256 :
      String

    t44Sha256IsCanonical :
      t44Sha256
      ≡
      "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"

    sha256ManifestPath :
      String

    artifactHeadersValidated :
      Bool

    artifactHeadersValidatedIsTrue :
      artifactHeadersValidated ≡ true

    rejectedRoutes :
      List HEPDataRatioTableArtifactRejectedRoute

    rejectedRoutesAreCanonical :
      rejectedRoutes
      ≡
      canonicalHEPDataRatioTableArtifactRejectedRoutes

    receiptNotes :
      List String

    remainingComparisonBlockers :
      List String

    nonPromotionBoundary :
      List HEPDataRatioTableArtifactReceiptBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataRatioTableArtifactReceiptBoundaries

    promotionReceiptBlocked :
      HEPDataRatioTableArtifactPromotionReceipt →
      ⊥

canonicalHEPDataRatioTableArtifactReceipt :
  HEPDataRatioTableArtifactReceipt
canonicalHEPDataRatioTableArtifactReceipt =
  record
    { status =
        checksumBoundT43T44ArtifactsAcquiredNoProjection
    ; priorRequest =
        R24.canonicalHEPDataRatioTableArtifactRequest
    ; checksumEntries =
        canonicalHEPDataRatioTableArtifactChecksumEntries
    ; checksumEntriesAreCanonical =
        refl
    ; t43Sha256 =
        "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"
    ; t43Sha256IsCanonical =
        refl
    ; t44Sha256 =
        "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"
    ; t44Sha256IsCanonical =
        refl
    ; sha256ManifestPath =
        "scripts/data/hepdata/ins2079374_t43_t44.sha256"
    ; artifactHeadersValidated =
        true
    ; artifactHeadersValidatedIsTrue =
        refl
    ; rejectedRoutes =
        canonicalHEPDataRatioTableArtifactRejectedRoutes
    ; rejectedRoutesAreCanonical =
        refl
    ; receiptNotes =
        "The short /t43 and /t44 endpoint forms were rejected after returning HEPData error HTML"
        ∷ "The name-based HEPData endpoint form returned CSV content with the expected table DOI headers"
        ∷ "The local t43/t44 artifacts are checksum-bound and can now be consumed by a future projection runner"
        ∷ []
    ; remainingComparisonBlockers =
        "accepted predictionFixedAt clean-freeze receipt"
        ∷ "digest-bound DASHI t43 projection runner implementation"
        ∷ "t43 projection run artifact with projectionDigest"
        ∷ "exact t43/t44 bin binding"
        ∷ "covariance-aware comparison-law receipt"
        ∷ []
    ; nonPromotionBoundary =
        canonicalHEPDataRatioTableArtifactReceiptBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; promotionReceiptBlocked =
        ratioTableArtifactPromotionImpossibleHere
    }

canonicalHEPDataRatioTableArtifactReceiptStatus :
  HEPDataRatioTableArtifactReceiptStatus
canonicalHEPDataRatioTableArtifactReceiptStatus =
  checksumBoundT43T44ArtifactsAcquiredNoProjection
