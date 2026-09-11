module DASHI.Biology.DrosophilaGautheyExternalManifestHashBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Biology.BioacousticFlySnowballParetoBidiExact as Snowball

------------------------------------------------------------------------
-- GAUTHEY EXTERNAL MANIFEST / HASH BIDI REFINEMENT
--
-- The public repository code-manifest is now exact at the inspected main tree.
-- This does NOT pay the external data-byte manifest needed for exact pooled-row
-- identity: the four aligned trial dictionaries and compact 940x668 carrier
-- still need exact bytes/digests.
------------------------------------------------------------------------

lightbeadRepositorySource : Attr.AttributedSource
lightbeadRepositorySource = Attr.mkNoDOISource
  "Murthy Lab"
  "lightbead-analysis"
  "GitHub primary software repository"
  "2026"
  "https://github.com/murthylab/lightbead-analysis"
  (Attr.namedSourceKind "primary software repository")
  "exact public code-manifest/custody source for Gauthey analysis and preprocessing; does not identify external dataset bytes"
  Attr.publicAttribution

gautheyDatasetSource : Attr.AttributedSource
gautheyDatasetSource = Attr.mkDOISource
  "Wayan Gauthey; Stephan Thiberge; Albert Lin et al."
  "Data for High-speed whole-brain imaging in Drosophila"
  "Zenodo / Princeton Data Commons"
  "2025"
  "10.34770/s5hx-1x75"
  "https://doi.org/10.34770/s5hx-1x75"
  Attr.archivalSource
  "alternate repository locator named by the Nature paper for the raw/preprocessed Gauthey data; locator identity does not pay individual file bytes or same-object hashes"
  Attr.publicAttribution

record ExactCodeManifest : Set where
  constructor exact-code-manifest
  field
    repositoryMainTreeSHA : String
    fig3AlignmentBlobSHA : String
    fig3PreprocessingBlobSHA : String
    functionsBlobSHA : String
    stimulusBlobSHA : String
    repositoryReference : String
    codeManifestPaid : Bool

open ExactCodeManifest public

canonicalExactCodeManifest : ExactCodeManifest
canonicalExactCodeManifest = exact-code-manifest
  "55570f4ad028bfd19ab63d5b9b13430803cb277c"
  "f34fe193f0507b5ad7f3c05d6b8973c04a34cf02"
  "39a4ae6739b9e13040b971469616e908df41f502"
  "436b785a2c33b12968c5645ff0118f4e5493cf10"
  "57a3052ba0a9b3503a04a6c50de5255fadcd4d19"
  "github:murthylab/lightbead-analysis main tree inspected through GitHub API"
  true

record ExternalDataManifestDebt : Set where
  constructor external-data-manifest-debt
  field
    rawRepresentativeDOI : String
    preprocessedAllTrialsDOI : String
    alternateRepositoryDOI : String
    requiredTrialFiles : List String
    compactCarrierReference : String
    trialBytesPaid : Bool
    trialSHA256Paid : Bool
    compactCarrierBytesPaid : Bool
    compactCarrierSHA256Paid : Bool

open ExternalDataManifestDebt public

canonicalExternalDataManifestDebt : ExternalDataManifestDebt
canonicalExternalDataManifestDebt = external-data-manifest-debt
  "10.5281/zenodo.17613016"
  "10.5281/zenodo.17618684"
  "10.34770/s5hx-1x75"
  ("GCaMP6f_12132024_a2_r2.pkl" ∷
   "GCaMP6f_12132024_a2_r3.pkl" ∷
   "GCaMP6f_12132024_a2_r4.pkl" ∷
   "GCaMP6f_12202024_a1_r2.pkl" ∷ [])
  "Data/Dffs/Audio correlated/dffs_audio_2p_corr_top05_all.pkl"
  false false false false

record ExternalManifestBidiReceipt : Set where
  constructor external-manifest-bidi-receipt
  field
    forwardPaidClaim : String
    reverseOpenDependency : String
    codeManifestMaySupportAlgorithmIdentity : Bool
    codeManifestPaysTrialBytes : Bool
    repositoryDOIPaysFileDigest : Bool
    exactDataDigestsStillRequiredForSameObjectWeld : Bool
    citationCreatesAuthority : Bool

open ExternalManifestBidiReceipt public

canonicalExternalManifestBidiReceipt : ExternalManifestBidiReceipt
canonicalExternalManifestBidiReceipt = external-manifest-bidi-receipt
  "the inspected public GitHub main tree fixes the exact analysis/alignment/preprocessing/functions/stimulus code objects used by the current reconstruction route"
  "acquire exact four source-trial bytes + SHA-256 and exact compact 940x668 carrier bytes + SHA-256 before paying the external-data same-object leaf"
  true false false true false

------------------------------------------------------------------------
-- Pareto interpretation.
--
-- This refines Snowball.exactExternalManifest into a paid code subleaf and an
-- unpaid data-byte subleaf. The parent remains live until the data bytes/digests
-- are paid; this owner does not mutate the base scheduler by fiat.
------------------------------------------------------------------------

parentParetoLeaf : Snowball.FrontierLeaf
parentParetoLeaf = Snowball.exactExternalManifest

codeSubleafPaid : Bool
codeSubleafPaid = true

dataByteSubleafPaid : Bool
dataByteSubleafPaid = false

nextExternalManifestAction : String
nextExternalManifestAction =
  "Use Zenodo/Princeton repository manifests to acquire the exact four named aligned trial dictionaries and compact selected-ROI carrier with content digests. Keep repository-level DOI/location metadata separate from file-byte identity."

record ExternalManifestBoundary : Set where
  constructor external-manifest-boundary
  field
    repositoryTreeIdentityEqualsExternalDataIdentity : Bool
    alternateRepositoryLocatorEqualsSameFileBytes : Bool
    codeBlobEqualityPaysDataSameObject : Bool
    exactDataHashCanPayDataSameObjectCoordinate : Bool
    codeManifestHistoryMustBeRetained : Bool
    dataDebtMayReopenROIIdentity : Bool

open ExternalManifestBoundary public

canonicalExternalManifestBoundary : ExternalManifestBoundary
canonicalExternalManifestBoundary = external-manifest-boundary
  false false false true true true
