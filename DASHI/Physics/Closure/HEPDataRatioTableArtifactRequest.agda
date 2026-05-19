module DASHI.Physics.Closure.HEPDataRatioTableArtifactRequest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- HEPData ratio table artifact request surface.
--
-- This module records the local state of the same-record HEPData ratio
-- artifacts for the t43/t44 lane.  It is diagnostic/request-only: no
-- artifact is fetched, no checksum is asserted, and no projection,
-- comparison, authority token, or W3/W4/W5/W8 promotion is constructed.

data HEPDataRatioTableArtifactRequestStatus : Set where
  supersededByChecksumBoundHEPR28Artifacts :
    HEPDataRatioTableArtifactRequestStatus

data HEPDataRatioTableArtifactRole : Set where
  lowMassPhistarMeasurementCached :
    HEPDataRatioTableArtifactRole
  lowMassPhistarCovarianceCached :
    HEPDataRatioTableArtifactRole
  lowMassToZPeakPhistarRatioAcquired :
    HEPDataRatioTableArtifactRole
  lowMassToZPeakPhistarRatioCovarianceAcquired :
    HEPDataRatioTableArtifactRole

data HEPDataRatioLocalArtifactState : Set where
  cachedUnderScriptsData :
    HEPDataRatioLocalArtifactState
  checksumBoundUnderScriptsData :
    HEPDataRatioLocalArtifactState

record HEPDataRatioTableArtifactEntry : Set where
  field
    role :
      HEPDataRatioTableArtifactRole

    localState :
      HEPDataRatioLocalArtifactState

    tableTitle :
      String

    tableDOI :
      String

    authoritativeDownloadURL :
      String

    expectedLocalPath :
      String

    checksumFieldRequiredBeforeUse :
      String

    currentChecksum :
      String

canonicalHEPDataRatioTableArtifactEntries :
  List HEPDataRatioTableArtifactEntry
canonicalHEPDataRatioTableArtifactEntries =
  record
    { role =
        lowMassPhistarMeasurementCached
    ; localState =
        cachedUnderScriptsData
    ; tableTitle =
        "phistar mass 50-76"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t19"
    ; authoritativeDownloadURL =
        "https://www.hepdata.net/download/table/ins2079374/Table%2019/csv"
    ; expectedLocalPath =
        "scripts/data/hepdata/ins2079374_phistar_mass_50-76_t19.csv"
    ; checksumFieldRequiredBeforeUse =
        "sourceCSVSha256"
    ; currentChecksum =
        "cached checksum recorded in HEPDataEmpiricalAuthorityReceiptCollation"
    }
  ∷ record
    { role =
        lowMassPhistarCovarianceCached
    ; localState =
        cachedUnderScriptsData
    ; tableTitle =
        "Covariance matrices for phistar mass 50-76"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t20"
    ; authoritativeDownloadURL =
        "https://www.hepdata.net/download/table/ins2079374/Table%2020/csv"
    ; expectedLocalPath =
        "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_t20.csv"
    ; checksumFieldRequiredBeforeUse =
        "sourceCovarianceCSVSha256"
    ; currentChecksum =
        "cached checksum recorded in HEPDataEmpiricalAuthorityReceiptCollation"
    }
  ∷ record
    { role =
        lowMassToZPeakPhistarRatioAcquired
    ; localState =
        checksumBoundUnderScriptsData
    ; tableTitle =
        "phistar mass 50-76 over mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t43"
    ; authoritativeDownloadURL =
        "https://www.hepdata.net/download/table/ins2079374/phistar%20mass%2050-76%20over%20mass%2076-106/csv"
    ; expectedLocalPath =
        "scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv"
    ; checksumFieldRequiredBeforeUse =
        "sourceRatioCSVSha256"
    ; currentChecksum =
        "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"
    }
  ∷ record
    { role =
        lowMassToZPeakPhistarRatioCovarianceAcquired
    ; localState =
        checksumBoundUnderScriptsData
    ; tableTitle =
        "Covariance matrices for phistar mass 50-76 over mass 76-106"
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t44"
    ; authoritativeDownloadURL =
        "https://www.hepdata.net/download/table/ins2079374/Covariance%20matrices%20for%20phistar%20mass%2050-76%20over%20mass%2076-106/csv"
    ; expectedLocalPath =
        "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv"
    ; checksumFieldRequiredBeforeUse =
        "sourceRatioCovarianceCSVSha256"
    ; currentChecksum =
        "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"
    }
  ∷ []

data HEPDataRatioRunAuthority : Set where

ratioRunAuthorityImpossibleHere :
  HEPDataRatioRunAuthority →
  ⊥
ratioRunAuthorityImpossibleHere ()

record HEPDataRatioTableArtifactRequest : Setω where
  field
    status :
      HEPDataRatioTableArtifactRequestStatus

    localArtifactEntries :
      List HEPDataRatioTableArtifactEntry

    localArtifactEntriesAreCanonical :
      localArtifactEntries
      ≡
      canonicalHEPDataRatioTableArtifactEntries

    localStateSummary :
      List String

    futureChecksumFieldsRequired :
      List String

    noProjectionComparisonRunRule :
      List String

    nonPromotionBoundary :
      List String

canonicalHEPDataRatioTableArtifactRequest :
  HEPDataRatioTableArtifactRequest
canonicalHEPDataRatioTableArtifactRequest =
  record
    { status =
        supersededByChecksumBoundHEPR28Artifacts
    ; localArtifactEntries =
        canonicalHEPDataRatioTableArtifactEntries
    ; localArtifactEntriesAreCanonical =
        refl
    ; localStateSummary =
        "t19 measurement artifact is cached under scripts/data/hepdata"
        ∷ "t20 covariance artifact is cached under scripts/data/hepdata"
        ∷ "t43 ratio artifact is present under scripts/data/hepdata and checksum-bound by HEP-R28"
        ∷ "t44 ratio covariance artifact is present under scripts/data/hepdata and checksum-bound by HEP-R28"
        ∷ "the short /t43, /t44, and Table 43 endpoint forms returned HEPData error HTML and must not be treated as valid CSV"
        ∷ []
    ; futureChecksumFieldsRequired =
        "sourceRatioCSVSha256 for t43 is supplied by HEP-R28"
        ∷ "sourceRatioCovarianceCSVSha256 for t44 is supplied by HEP-R28"
        ∷ "cachedRatioArtifactSha256 for the local t43 artifact is supplied by HEP-R28"
        ∷ "cachedRatioCovarianceArtifactSha256 for the local t44 artifact is supplied by HEP-R28"
        ∷ "download URL, table DOI, local path, and checksum are bound in HEPDataRatioTableArtifactReceipt"
        ∷ []
    ; noProjectionComparisonRunRule =
        "Projection may not begin from checksums alone; it still requires predictionFixedAt, runner implementation, projection digest, and bin binding"
        ∷ "Comparison may not begin from checksums alone; it still requires projection output and a comparison-law receipt"
        ∷ "A DOI, URL, table title, or expected path is not an artifact checksum receipt"
        ∷ "The cached t19/t20 artifacts do not authorize substituting, deriving, or projecting t43/t44; use the HEP-R28 checksum-bound ratio artifacts"
        ∷ []
    ; nonPromotionBoundary =
        "No authority token is constructed here"
        ∷ "No projection receipt is constructed here"
        ∷ "No comparison-law receipt is constructed here"
        ∷ "No W3, W4, W5, or W8 promotion follows from this request surface"
        ∷ []
    }
