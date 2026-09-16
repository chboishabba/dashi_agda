module DASHI.Reasoning.MaleCNSIndependentReplicationAcquisitionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- LIVE INDEPENDENT-REPLICATION ACQUISITION FRONTIER
--
-- This owner records source/acquisition state only.  It does not turn exact
-- source-trace identity recovery into atlas identity, independent replication,
-- biological mechanism, or population generalisation.
------------------------------------------------------------------------

record TrialIdentityCount : Set where
  constructor trial-identity-count
  field
    trialIdentity : String
    exactSelectedRowsRecovered : Nat
    trialActuallySearched : Bool

open TrialIdentityCount public

a2r5IdentityCount : TrialIdentityCount
a2r5IdentityCount = trial-identity-count "04032024_6f_a2_r5" 374 true

a1r9IdentityCount : TrialIdentityCount
a1r9IdentityCount = trial-identity-count "04192024_6f_a1_r9" 185 true

a1r2IdentityCount : TrialIdentityCount
a1r2IdentityCount = trial-identity-count "04192024_6f_a1_r2" 300 true

a1r6IdentityCount : TrialIdentityCount
a1r6IdentityCount = trial-identity-count "04192024_6f_a1_r6" 192 true

a1r1IdentityCount : TrialIdentityCount
a1r1IdentityCount = trial-identity-count "04162024_6f_a1_r1" 158 true

a2r1SearchedZeroIdentityCount : TrialIdentityCount
a2r1SearchedZeroIdentityCount = trial-identity-count "04032024_6f_a2_r1" 0 true

allSixTrialsSearched : Bool
allSixTrialsSearched = true

resolvedSelectedRows : Nat
resolvedSelectedRows = 1209

unresolvedSelectedRows : Nat
unresolvedSelectedRows = 411

depositedSelectedRows : Nat
depositedSelectedRows = 1620

runtimeRepository : String
runtimeRepository = "github.com/chboishabba/dashiBRAIN"

runtimeBranch : String
runtimeBranch = "agent/malecns-real-benchmark-tranche"

runtimeHead : String
runtimeHead = "5752ad525d707b70f483f6359f3b5f34efff1586"

accumulationReceiptPath : String
accumulationReceiptPath =
  "data/gauthey_lbm/reconstruction_all_available/gauthey_lbm_identity_accumulation.json"

------------------------------------------------------------------------
-- Public source attribution.  These sources pay only the bounded deposition
-- and processing statements named below; citation imports neither proof nor
-- authority.
------------------------------------------------------------------------

gautheyPaper : Source.AttributedSource
gautheyPaper = Source.mkDOISource
  "Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy; Stephan Y. Thiberge"
  "High-speed whole-brain imaging in Drosophila"
  "Nature Communications 17:5810"
  "2026"
  "10.1038/s41467-026-72437-1"
  "https://doi.org/10.1038/s41467-026-72437-1"
  Source.academicArticleSource
  "Pays the bounded public data-availability statement: raw data are deposited for a representative trial, while preprocessed data are deposited for all trials. It does not prove that a missing same-trial anatomical carrier cannot exist elsewhere."
  Source.publicAttribution

gautheyAnalysisRepository : Source.AttributedSource
gautheyAnalysisRepository = Source.mkNoDOISource
  "Murthy Lab / Gauthey et al."
  "lightbead-analysis"
  "GitHub source repository"
  "2026 snapshot"
  "https://github.com/murthylab/lightbead-analysis"
  (Source.namedSourceKind "scientific software repository")
  "Pays the bounded pipeline statement that batch_tiff_to_dff_mean_brain_RigE.sh creates a mean brain from raw TIFF input before downstream motion-correction and signal extraction. Historical commits additionally preserve Princeton HPC processing paths; those paths are provenance coordinates, not public access receipts."
  Source.publicAttribution

princetonDataCommons : Source.AttributedSource
princetonDataCommons = Source.mkDOISource
  "Princeton University / Gauthey et al."
  "Data for High-speed whole-brain imaging in Drosophila"
  "Princeton Data Commons"
  "2025"
  "10.34770/s5hx-1x75"
  "https://doi.org/10.34770/s5hx-1x75"
  (Source.namedSourceKind "research data repository")
  "Pays only the public mirror/repository coordinate for the deposited Gauthey data. Generic Princeton Data Commons Globus support for large deposits does not create a dataset-specific public Globus endpoint or non-discovery raw/anatomical carrier."
  Source.publicAttribution

replicationAcquisitionSourceAtlas : Source.AttributedSourceAtlas
replicationAcquisitionSourceAtlas = Source.mkSourceAtlas
  "MaleCNS Gauthey independent-replication acquisition sources"
  "DASHI.Reasoning.MaleCNSIndependentReplicationAcquisitionFrontierExact"
  (gautheyPaper ∷ gautheyAnalysisRepository ∷ princetonDataCommons ∷ [])
  "Source-bounded data-availability, repository-mirror, processing-pipeline and historical-path provenance only; empirical counts come from dashiBRAIN runtime receipts."

------------------------------------------------------------------------
-- Public-access archaeology boundary.
------------------------------------------------------------------------

record PublicAccessArchaeologyBoundary : Set where
  constructor public-access-archaeology-boundary
  field
    representativeRawPublic : Bool
    allTrialPreprocessedPublic : Bool
    princetonMirrorAdvertised : Bool
    pdcGenericGlobusSupportObserved : Bool
    historicalPrincetonHPCNamespaceObserved : Bool
    historicalPrincetonHPCNamespace : String
    publicNonDiscoveryRawRouteObserved : Bool
    publicNonDiscoveryAnatomyRouteObserved : Bool
    datasetSpecificPublicGlobusEndpointObserved : Bool
    internalHPCPathCreatesPublicAccessReceipt : Bool
    genericGlobusSupportCreatesDatasetAccessReceipt : Bool
    archaeologyPaysSameTrialAnatomy : Bool
    interpretation : String

open PublicAccessArchaeologyBoundary public

canonicalPublicAccessArchaeologyBoundary : PublicAccessArchaeologyBoundary
canonicalPublicAccessArchaeologyBoundary = public-access-archaeology-boundary
  true
  true
  true
  true
  true
  "/scratch/gpfs/albertl/rigE_data/"
  false
  false
  false
  false
  false
  false
  "Historical lightbead-analysis commits expose Princeton internal processing namespaces and trial-like file paths, while Princeton Data Commons generically supports Globus for large deposits. The current public audit did not locate a dataset-specific public Globus endpoint, non-discovery raw TIFF carrier, anatomical/reference volume, or saved same-trial transform. Internal HPC paths and generic transfer infrastructure are discovery/provenance coordinates only; neither pays public access or same-object registration. This bounded audit does not prove that private or unindexed files do not exist."

------------------------------------------------------------------------
-- a1_r1 route-A inspection boundary.
------------------------------------------------------------------------

record A1R1ContainerInspectionReceipt : Set where
  constructor a1r1-container-inspection-receipt
  field
    trialIdentity : String
    exactSourceRowsRecovered : Nat
    functionalArraysPresent : Bool
    timingAndStimulusMetadataPresent : Bool
    imageOrVolumePresent : Bool
    secondImagingChannelPresent : Bool
    roiSpatialCoordinatesPresent : Bool
    transformOrDeformationPresent : Bool
    atlasReferencePresent : Bool
    sameTrialAnatomyRecoveredFromContainer : Bool
    interpretation : String

open A1R1ContainerInspectionReceipt public

a1r1ContainerInspectionReceipt : A1R1ContainerInspectionReceipt
a1r1ContainerInspectionReceipt = a1r1-container-inspection-receipt
  "04162024_6f_a1_r1"
  158
  true
  true
  false
  false
  false
  false
  false
  false
  "The inspected preprocessed a1_r1 payload contains functional ROI-by-time arrays and timing/stimulus metadata but no observed anatomy, spatial ROI coordinates, transform, deformation field, or atlas reference. This closes only the in-container route; it does not prove that no authoritative external same-trial anatomy exists."

------------------------------------------------------------------------
-- Promotion firewall / actual current wall.
------------------------------------------------------------------------

record IndependentReplicationAcquisitionBoundary : Set where
  constructor independent-replication-acquisition-boundary
  field
    allSixSourceTrialsSearched : Bool
    exactIdentityRecoveryComplete : Bool
    searchedZeroMeansNoBiologicalContribution : Bool
    nativeFieldsCanBeMaterializedForRecoveredNonzeroTrials : Bool
    a1r1PreprocessedContainerPaysSameTrialAnatomy : Bool
    publicRepresentativeRawDepositPaysA1R1Anatomy : Bool
    historicalInternalPathPaysSameTrialAnatomy : Bool
    genericPDCGlobusSupportPaysDatasetSpecificAccess : Bool
    sameRegionLabelsAuthorizeFrozenEncoderReuse : Bool
    sameTrialAnatomyOrExecutedTransformStillRequired : Bool
    registeredIndependentReplicationPaid : Bool
    crossAnimalGeneralizationPaid : Bool
    interpretation : String

open IndependentReplicationAcquisitionBoundary public

canonicalIndependentReplicationAcquisitionBoundary :
  IndependentReplicationAcquisitionBoundary
canonicalIndependentReplicationAcquisitionBoundary =
  independent-replication-acquisition-boundary
    true
    false
    false
    true
    false
    false
    false
    false
    false
    true
    false
    false
    "Live frontier: all six Gauthey LBM source trials have been searched and 1209/1620 selected rows have exact source-trace identities. Public-source archaeology now additionally resolves the historical Princeton processing namespace and the Princeton Data Commons mirror/Globus context, but no dataset-specific public non-discovery raw/anatomy/transform route was observed. The first independent common-atlas replication therefore remains blocked on a same-trial anatomical image or equivalent executed transform receipt for a non-discovery recording."
