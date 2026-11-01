module DASHI.Biology.DrosophilaGautheyRegistrationStagingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PURPOSE
--
-- Formal receipt surface for the now-explicit registration chain discovered
-- from the Gauthey compact deposit and BIFROST repository.
--
-- Scientific sources:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1; data DOI 10.5281/zenodo.17618684.
--
-- Bella E. Brezovec et al.,
-- "BIFROST: A method for registering diverse imaging datasets of the
-- Drosophila brain", DOI 10.1073/pnas.2322687121;
-- data DOI 10.5061/dryad.8pk0p2nx1.
--
-- These sources identify data/method producers only. They do not prove the
-- DASHI same-object statements below.
------------------------------------------------------------------------

record RegistrationStage : Set where
  constructor registrationStage
  field
    sourceSpace : String
    targetSpace : String
    transformIdentifier : String
    transformVerified : Bool
    note : String

open RegistrationStage public

trialMeanBrainToFDA : RegistrationStage
trialMeanBrainToFDA = registrationStage
  "gauthey_trial_mean_brain"
  "bifrost_fda"
  "UNRESOLVED"
  false
  "No exact trial-mean-brain to FDA transform is pinned yet"

fdaToJRC2018 : RegistrationStage
fdaToJRC2018 = registrationStage
  "bifrost_fda"
  "JRC2018_female"
  "doi:10.5061/dryad.8pk0p2nx1#thresholded_FDA_to_JRC2018_female.h5"
  true
  "Repository-verified BIFROST source transform; not yet a local benchmark output"

record GautheyCentroidReceipt : Set where
  constructor gautheyCentroidReceipt
  field
    labelsArchiveMember : String
    meanBrainArchiveMember : String
    outputCoordinateSpace : String
    evidenceKind : String
    sourceDatasetIdentifier : String

open GautheyCentroidReceipt public

canonicalGautheyCentroidReceipt : GautheyCentroidReceipt
canonicalGautheyCentroidReceipt = gautheyCentroidReceipt
  "Data/Labels/04032024_6f_a2_r5_n2000_labels.h5"
  "Data/Mean brain/04032024_GCamp6f_a2_r5_w3_mean_G.nii"
  "gauthey_trial_mean_brain"
  "segmentation_label_centroid_unregistered_to_functional_trace"
  "doi:10.5281/zenodo.17618684"

record GautheyRegistrationBoundary : Set where
  constructor gautheyRegistrationBoundary
  field
    segmentationLabelDoesNotIdentifyFunctionalColumn : Bool
    trialMeanBrainDoesNotEqualFDA : Bool
    fdaToJRC2018DoesNotSupplyTrialToFDA : Bool
    jrc2018CoordinateDoesNotIdentifyMaleCNSNeuron : Bool
    centroidDerivationDoesNotPromoteRegionAssignment : Bool
    completeChainRequiresEveryTransformReceipt : Bool

open GautheyRegistrationBoundary public

canonicalGautheyRegistrationBoundary : GautheyRegistrationBoundary
canonicalGautheyRegistrationBoundary =
  gautheyRegistrationBoundary true true true true true true
