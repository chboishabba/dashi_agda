module DASHI.Biology.DrosophilaGautheyCompactArchiveReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Runtime/source-derived receipt for selectively accessible Gauthey artifacts.
--
-- Scientific source:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1;
-- preprocessed data DOI 10.5281/zenodo.17618684;
-- analysis code github:murthylab/lightbead-analysis.
--
-- Source correction: fig3_preprocessing.py sets min_dim = 668 for the 2p lane,
-- slices dffs_corrected[:, :668], vertically stacks ROI rows across four trials,
-- and exports dffs_all[audio_correlated, :]. Thus deposited 940 x 668 means
-- 940 selected ROI rows x 668 time samples, not 668 functional units.
------------------------------------------------------------------------

record GautheyCompactArchiveReceipt : Set where
  constructor gautheyCompactArchiveReceipt
  field
    paperDOI : String
    datasetDOI : String
    codeRepository : String
    archiveName : String
    functionalMember : String
    sourceArrayRows : Nat
    sourceArrayColumns : Nat
    selectedROIRows : Nat
    timeSamples : Nat
    sourceAxisSemantics : String
    remoteRangeSelectable : Bool
    selectedROIIdentityRegistered : Bool

open GautheyCompactArchiveReceipt public

canonicalGautheyCompactArchiveReceipt : GautheyCompactArchiveReceipt
canonicalGautheyCompactArchiveReceipt =
  gautheyCompactArchiveReceipt
    "10.1038/s41467-026-72437-1"
    "10.5281/zenodo.17618684"
    "github:murthylab/lightbead-analysis"
    "Data.zip"
    "Data/Dffs/Audio correlated/dffs_audio_2p_corr_top05_all.pkl"
    940
    668
    940
    668
    "selected-roi-by-time"
    true
    false

record GautheyCompactArchiveBoundary : Set where
  constructor gautheyCompactArchiveBoundary
  field
    selectiveRangeExtractionDoesNotRequireFullArchive : Bool
    sourceArrayColumnDoesNotMeanFunctionalUnit : Bool
    selectedROIRowDoesNotNameSourceROI : Bool
    pooled2PMatrixDoesNotInheritLBCompanionIdentity : Bool
    sourceSelectionIndicesNeedRecovery : Bool

canonicalGautheyCompactArchiveBoundary : GautheyCompactArchiveBoundary
canonicalGautheyCompactArchiveBoundary =
  gautheyCompactArchiveBoundary true true true true true
