module DASHI.Biology.DrosophilaGautheyCompactArchiveReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Runtime-derived receipt for selectively accessible members of Gauthey et al.
--
-- Scientific source:
--   Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
--   Stephan Y. Thiberge,
--   "High-speed whole-brain imaging in Drosophila",
--   DOI 10.1038/s41467-026-72437-1.
--   Preprocessed data DOI 10.5281/zenodo.17618684.
--
-- These fields record archive identity and observed runtime structure only.
-- They do not promote archive-array indices to anatomical ROI/neuron identity.
------------------------------------------------------------------------

record GautheyCompactArchiveReceipt : Set where
  constructor gautheyCompactArchiveReceipt
  field
    paperDOI : String
    datasetDOI : String
    archiveName : String
    functionalMember : String
    functionalRows : Nat
    functionalColumns : Nat
    responsiveROIListMember : String
    labelsMember : String
    meanBrainMember : String
    remoteRangeSelectable : Bool
    fullArchiveDownloadRequired : Bool
    archiveUnitIdentityRegistered : Bool

open GautheyCompactArchiveReceipt public

canonicalGautheyCompactArchiveReceipt : GautheyCompactArchiveReceipt
canonicalGautheyCompactArchiveReceipt =
  gautheyCompactArchiveReceipt
    "10.1038/s41467-026-72437-1"
    "10.5281/zenodo.17618684"
    "Data.zip"
    "Data/Dffs/Audio correlated/dffs_audio_2p_corr_top05_all.pkl"
    940
    668
    "Data/Mean brain/audio_roi_04032024_6f_a2_r5_pval.csv"
    "Data/Labels/04032024_6f_a2_r5_n2000_labels.h5"
    "Data/Mean brain/04032024_GCamp6f_a2_r5_w3_mean_G.nii"
    true
    true
    false

record GautheyCompactArchiveBoundary : Set where
  constructor gautheyCompactArchiveBoundary
  field
    selectiveRangeExtractionDoesNotRequireFullArchive : Bool
    preprocessedMatrixDoesNotNameAnatomicalUnits : Bool
    responsiveROIListDoesNotAutomaticallyIndexFunctionalMatrix : Bool
    segmentationLabelsDoNotAutomaticallyProvideJRC2018Regions : Bool
    meanBrainVolumeStillRequiresRegistrationTransform : Bool

canonicalGautheyCompactArchiveBoundary : GautheyCompactArchiveBoundary
canonicalGautheyCompactArchiveBoundary =
  gautheyCompactArchiveBoundary true true true true true
