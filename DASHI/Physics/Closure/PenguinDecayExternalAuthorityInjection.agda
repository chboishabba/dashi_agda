module DASHI.Physics.Closure.PenguinDecayExternalAuthorityInjection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Gate 5 penguin external authority/freeze evidence injection.
--
-- This module records only evidence that was directly available from local
-- commands or network lookups.  The PyPI flavio package hashes are populated,
-- and the CMS HEPData record metadata JSON is checksum-bound.  The selected
-- HEPData likelihood table bytes are still not populated because the local
-- artifact is record metadata, not the table payload.

data PenguinExternalAuthorityInjectionStatus : Set where
  flavioHashesPopulatedHEPDataTableHashesStillGapFreezeFormulaRecorded :
    PenguinExternalAuthorityInjectionStatus

  flavioAndCMSRecordMetadataPopulatedTablePayloadStillGap :
    PenguinExternalAuthorityInjectionStatus

  datasetSMWilsonAttestationPopulatedCleanCodeHeadStillGap :
    PenguinExternalAuthorityInjectionStatus

data PenguinExternalAuthorityBoundary : Set where
  noHEPDataTableSHA256Fabricated :
    PenguinExternalAuthorityBoundary
  noAcceptedHEPDataAuthorityTokenHere :
    PenguinExternalAuthorityBoundary
  noAcceptedCleanFreezeHere :
    PenguinExternalAuthorityBoundary
  noPenguinEmpiricalPromotionHere :
    PenguinExternalAuthorityBoundary

canonicalPenguinExternalAuthorityBoundaries :
  List PenguinExternalAuthorityBoundary
canonicalPenguinExternalAuthorityBoundaries =
  noHEPDataTableSHA256Fabricated
  ∷ noAcceptedHEPDataAuthorityTokenHere
  ∷ noAcceptedCleanFreezeHere
  ∷ noPenguinEmpiricalPromotionHere
  ∷ []

data AcceptedPenguinExternalAuthorityToken : Set where

acceptedPenguinExternalAuthorityTokenImpossibleHere :
  AcceptedPenguinExternalAuthorityToken →
  ⊥
acceptedPenguinExternalAuthorityTokenImpossibleHere ()

record HEPDataPenguinLookupReceipt : Set where
  constructor mkHEPDataPenguinLookupReceipt
  field
    requestedIdentifier :
      String

    requestedIdentifierKind :
      String

    intendedAuthorityRole :
      String

    primaryRetrievalURL :
      String

    retrievalFindings :
      List String

    inspireFinding :
      String

    hepdataRecordOrTableIdentifierDirectlyResolved :
      Bool

    hepdataRecordOrTableIdentifierDirectlyResolvedIsFalse :
      hepdataRecordOrTableIdentifierDirectlyResolved ≡ false

    hepdataTableSHA256DirectlyObtained :
      Bool

    hepdataTableSHA256DirectlyObtainedIsFalse :
      hepdataTableSHA256DirectlyObtained ≡ false

    populatedTableSHA256 :
      String

    populatedTableSHA256IsGap :
      populatedTableSHA256
      ≡
      "gap: no directly obtained HEPData table SHA256 for this requested identifier"

    remainingGap :
      String

open HEPDataPenguinLookupReceipt public

hepdataIns2000945LookupReceipt :
  HEPDataPenguinLookupReceipt
hepdataIns2000945LookupReceipt =
  mkHEPDataPenguinLookupReceipt
    "ins2000945"
    "requested HEPData/INSPIRE-style identifier"
    "candidate LHCb penguin external dataset authority"
    "https://www.hepdata.net/record/ins2000945"
    ( "GET https://www.hepdata.net/record/ins2000945 returned HTTP 404 HTML"
      ∷ "GET https://www.hepdata.net/search/?q=ins2000945&format=json returned HTTP 403 Cloudflare challenge"
      ∷ "GET https://www.hepdata.net/download/submission/ins2000945/1/yaml returned HTTP 403 Cloudflare challenge"
      ∷ "GET https://inspirehep.net/api/literature/2000945 returned HTTP 404"
      ∷ "GET https://inspirehep.net/api/literature?q=recid:2000945 returned zero hits"
      ∷ [] )
    "No INSPIRE literature record with recid 2000945 was resolved by the tested INSPIRE API calls."
    false
    refl
    false
    refl
    "gap: no directly obtained HEPData table SHA256 for this requested identifier"
    refl
    "Need a resolvable HEPData record/table DOI or downloadable table artifact before any table SHA256 can be encoded."

hepdataIns1394303LookupReceipt :
  HEPDataPenguinLookupReceipt
hepdataIns1394303LookupReceipt =
  mkHEPDataPenguinLookupReceipt
    "ins1394303"
    "requested HEPData/INSPIRE-style identifier"
    "candidate LHCb penguin external dataset authority"
    "https://www.hepdata.net/record/ins1394303"
    ( "GET https://www.hepdata.net/record/ins1394303 returned HTTP 404 HTML"
      ∷ "GET https://www.hepdata.net/search/?q=ins1394303&format=json returned HTTP 403 Cloudflare challenge"
      ∷ "GET https://www.hepdata.net/download/submission/ins1394303/1/yaml returned HTTP 403 Cloudflare challenge"
      ∷ "GET https://inspirehep.net/api/literature/1394303 returned an INSPIRE record, not a HEPData table payload"
      ∷ [] )
    "INSPIRE recid 1394303 resolves to 'The Resistive-WELL detector: a compact spark-protected single', DOI 10.22323/1.238.0024; it is not evidence for an LHCb b -> s mu+ mu- penguin table."
    false
    refl
    false
    refl
    "gap: no directly obtained HEPData table SHA256 for this requested identifier"
    refl
    "Need the actual LHCb HEPData record/table DOI or downloadable table artifact; the tested identifier did not provide a penguin table checksum."

record CMSHEPDataTableMetadata : Set where
  constructor mkCMSHEPDataTableMetadata
  field
    tableName :
      String

    tableDOI :
      String

    tableId :
      String

    tableRole :
      String

    yamlURL :
      String

    jsonURL :
      String

open CMSHEPDataTableMetadata public

cmsResultsTableMetadata :
  CMSHEPDataTableMetadata
cmsResultsTableMetadata =
  mkCMSHEPDataTableMetadata
    "Results"
    "10.17182/hepdata.135675.v1/t1"
    "1435213"
    "scalar results table: measured Bs to mu+mu- branching fraction, effective lifetime, and B0 upper limits"
    "https://www.hepdata.net/download/table/ins2616304/Results/yaml"
    "https://www.hepdata.net/download/table/ins2616304/Results/json"

cmsFigure4cTableMetadata :
  CMSHEPDataTableMetadata
cmsFigure4cTableMetadata =
  mkCMSHEPDataTableMetadata
    "Figure 4-c"
    "10.17182/hepdata.135675.v1/t4"
    "1435216"
    "2D profile likelihood scan as a function of Bs to mu+mu- and B0 to mu+mu- branching fractions"
    "https://www.hepdata.net/download/table/ins2616304/Figure 4-c/yaml"
    "https://www.hepdata.net/download/table/ins2616304/Figure 4-c/json"

record CMSHEPDataRecordMetadataReceipt : Set where
  constructor mkCMSHEPDataRecordMetadataReceipt
  field
    selectedDatasetArtifact :
      String

    selectedDatasetArtifactIsCanonical :
      selectedDatasetArtifact ≡ "HEPData:ins2616304:v1"

    localMetadataPath :
      String

    localMetadataPathIsCanonical :
      localMetadataPath ≡ "/home/c/Downloads/ins2616304.json"

    metadataSHA256 :
      String

    metadataSHA256IsCanonical :
      metadataSHA256
      ≡
      "aead05303abe7b471279cd33b8b2abc0005017d062c3ec48386ff2979fe3ed52"

    recordDOI :
      String

    recordDOIIsCanonical :
      recordDOI ≡ "10.17182/hepdata.135675.v1"

    inspireIdentifier :
      String

    inspireIdentifierIsCanonical :
      inspireIdentifier ≡ "ins2616304"

    arxivIdentifier :
      String

    arxivIdentifierIsCanonical :
      arxivIdentifier ≡ "arXiv:2212.10311"

    publicationDOI :
      String

    publicationDOIIsCanonical :
      publicationDOI ≡ "10.1016/j.physletb.2023.137955"

    collaboration :
      String

    collaborationIsCMS :
      collaboration ≡ "CMS"

    resultsTable :
      CMSHEPDataTableMetadata

    resultsTableDOIIsCanonical :
      tableDOI resultsTable ≡ "10.17182/hepdata.135675.v1/t1"

    profileLikelihoodTable :
      CMSHEPDataTableMetadata

    profileLikelihoodTableDOIIsCanonical :
      tableDOI profileLikelihoodTable ≡ "10.17182/hepdata.135675.v1/t4"

    recordMetadataChecksumPopulated :
      Bool

    recordMetadataChecksumPopulatedIsTrue :
      recordMetadataChecksumPopulated ≡ true

    profileLikelihoodTablePayloadSHA256Populated :
      Bool

    profileLikelihoodTablePayloadSHA256PopulatedIsTrue :
      profileLikelihoodTablePayloadSHA256Populated ≡ true

    profileLikelihoodTablePayloadSHA256 :
      String

    profileLikelihoodTablePayloadSHA256IsCanonical :
      profileLikelihoodTablePayloadSHA256
      ≡
      "9fb80a95fb4b600e3490e47cf150c537b9b66699536c3caed2abe74f307ccb59"

    profileLikelihoodTablePayloadPath :
      String

    profileLikelihoodTablePayloadPathIsCanonical :
      profileLikelihoodTablePayloadPath
      ≡
      "/home/c/Downloads/HEPData-ins2616304-v1.zip:contour_hist.yaml"

    resultsTablePayloadSHA256 :
      String

    resultsTablePayloadSHA256IsCanonical :
      resultsTablePayloadSHA256
      ≡
      "08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"

    resultsTablePayloadPath :
      String

    resultsTablePayloadPathIsCanonical :
      resultsTablePayloadPath
      ≡
      "/home/c/Downloads/HEPData-ins2616304-v1.zip:results.yaml"

    submissionArchiveSHA256 :
      String

    submissionArchiveSHA256IsCanonical :
      submissionArchiveSHA256
      ≡
      "561babac1c964306c4c06f1f862d8db3ca4f46fdc3ee071c88eb81887a258bc4"

    cmsMetadataNotes :
      List String

open CMSHEPDataRecordMetadataReceipt public

canonicalCMSHEPDataRecordMetadataReceipt :
  CMSHEPDataRecordMetadataReceipt
canonicalCMSHEPDataRecordMetadataReceipt =
  mkCMSHEPDataRecordMetadataReceipt
    "HEPData:ins2616304:v1"
    refl
    "/home/c/Downloads/ins2616304.json"
    refl
    "aead05303abe7b471279cd33b8b2abc0005017d062c3ec48386ff2979fe3ed52"
    refl
    "10.17182/hepdata.135675.v1"
    refl
    "ins2616304"
    refl
    "arXiv:2212.10311"
    refl
    "10.1016/j.physletb.2023.137955"
    refl
    "CMS"
    refl
    cmsResultsTableMetadata
    refl
    cmsFigure4cTableMetadata
    refl
    true
    refl
    true
    refl
    "9fb80a95fb4b600e3490e47cf150c537b9b66699536c3caed2abe74f307ccb59"
    refl
    "/home/c/Downloads/HEPData-ins2616304-v1.zip:contour_hist.yaml"
    refl
    "08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"
    refl
    "/home/c/Downloads/HEPData-ins2616304-v1.zip:results.yaml"
    refl
    "561babac1c964306c4c06f1f862d8db3ca4f46fdc3ee071c88eb81887a258bc4"
    refl
    ( "Local /home/c/Downloads/ins2616304.json is the HEPData record metadata JSON and has SHA256 aead05303abe7b471279cd33b8b2abc0005017d062c3ec48386ff2979fe3ed52"
      ∷ "Table t1 Results resolves as 10.17182/hepdata.135675.v1/t1 with table id 1435213"
      ∷ "Table t4 Figure 4-c resolves as 10.17182/hepdata.135675.v1/t4 with table id 1435216 and is the 2D profile likelihood surface"
      ∷ "Local /home/c/Downloads/HEPData-ins2616304-v1.zip has SHA256 561babac1c964306c4c06f1f862d8db3ca4f46fdc3ee071c88eb81887a258bc4"
      ∷ "The t4 Figure 4-c YAML payload is contour_hist.yaml and has SHA256 9fb80a95fb4b600e3490e47cf150c537b9b66699536c3caed2abe74f307ccb59"
      ∷ "The t1 Results YAML payload is results.yaml and has SHA256 08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb"
      ∷ [] )

record FlavioPyPIArtifactHashReceipt : Set where
  constructor mkFlavioPyPIArtifactHashReceipt
  field
    packageName :
      String

    packageNameIsFlavio :
      packageName ≡ "flavio"

    version :
      String

    versionIsCanonical :
      version ≡ "2.7.0"

    pypiJSONURL :
      String

    pypiJSONURLIsCanonical :
      pypiJSONURL ≡ "https://pypi.org/pypi/flavio/2.7.0/json"

    wheelFilename :
      String

    wheelFilenameIsCanonical :
      wheelFilename ≡ "flavio-2.7.0-py3-none-any.whl"

    wheelSHA256 :
      String

    wheelSHA256IsCanonical :
      wheelSHA256
      ≡
      "3d5aaeb5a9df7c479949e4641ccbd2dc662cb010aabf9dda5f725a8a80813b4f"

    wheelURL :
      String

    sdistFilename :
      String

    sdistFilenameIsCanonical :
      sdistFilename ≡ "flavio-2.7.0.tar.gz"

    sdistSHA256 :
      String

    sdistSHA256IsCanonical :
      sdistSHA256
      ≡
      "08c9c9608ae2ee76d4097b5836e7ca2479f59f9478d0fdddb2cf01b7da4e796e"

    sdistURL :
      String

    pypiHashesPopulated :
      Bool

    pypiHashesPopulatedIsTrue :
      pypiHashesPopulated ≡ true

open FlavioPyPIArtifactHashReceipt public

canonicalFlavioPyPIArtifactHashReceipt :
  FlavioPyPIArtifactHashReceipt
canonicalFlavioPyPIArtifactHashReceipt =
  mkFlavioPyPIArtifactHashReceipt
    "flavio"
    refl
    "2.7.0"
    refl
    "https://pypi.org/pypi/flavio/2.7.0/json"
    refl
    "flavio-2.7.0-py3-none-any.whl"
    refl
    "3d5aaeb5a9df7c479949e4641ccbd2dc662cb010aabf9dda5f725a8a80813b4f"
    refl
    "https://files.pythonhosted.org/packages/9f/1b/65f99b93875e4e5c0361b73723672407b134752713005dd384b3ce4729b9/flavio-2.7.0-py3-none-any.whl"
    "flavio-2.7.0.tar.gz"
    refl
    "08c9c9608ae2ee76d4097b5836e7ca2479f59f9478d0fdddb2cf01b7da4e796e"
    refl
    "https://files.pythonhosted.org/packages/e0/de/4ff4c8199136c255473a1cc9c60a63dcac7ad2abd8bdad48478d9253954b/flavio-2.7.0.tar.gz"
    true
    refl

record PenguinRuntimeAuthorityArtifactReceipt : Set where
  constructor mkPenguinRuntimeAuthorityArtifactReceipt
  field
    smBaselineManifestPath :
      String

    smBaselineManifestSHA256 :
      String

    smBaselineManifestSHA256IsCanonical :
      smBaselineManifestSHA256
      ≡
      "469aaab75326d6f39678783d8b32b6be22a6b299c43043865eb1679d259dd476"

    smRuntimeSnapshotPath :
      String

    smRuntimeSnapshotSHA256 :
      String

    smRuntimeSnapshotSHA256IsCanonical :
      smRuntimeSnapshotSHA256
      ≡
      "fa690ebff9fa508cf553671e5d8f5fb98e3718c4643fabfb0459dc56a0e8ccda"

    smPredictionObservable :
      String

    smPredictionObservableIsCanonical :
      smPredictionObservable ≡ "BR(Bs->mumu)"

    smPredictionValueText :
      String

    smPredictionValueTextIsCanonical :
      smPredictionValueText ≡ "3.6289314570849374e-09"

    wilsonAuthorityManifestPath :
      String

    wilsonAuthorityManifestSHA256 :
      String

    wilsonAuthorityManifestSHA256IsCanonical :
      wilsonAuthorityManifestSHA256
      ≡
      "f443742a9207a8b1493b84934e21a7c980839434c49257e0bb649077aafd4585"

    wilsonVersion :
      String

    wilsonVersionIsCanonical :
      wilsonVersion ≡ "2.5.2"

    wilsonWheelSHA256 :
      String

    wilsonWheelSHA256IsCanonical :
      wilsonWheelSHA256
      ≡
      "959e3dbd6bfefb43b3769fe07e2d8e59c153abe6796851fb91c4d18b7981799a"

    ckmSourceCommitOrRevision :
      String

    ckmSourceCommitOrRevisionIsFlavioWheel :
      ckmSourceCommitOrRevision
      ≡
      "flavio-2.7.0-wheel-sha256:3d5aaeb5a9df7c479949e4641ccbd2dc662cb010aabf9dda5f725a8a80813b4f"

    projectionRunnerManifestPath :
      String

    projectionRunnerManifestSHA256 :
      String

    projectionRunnerManifestSHA256IsCanonical :
      projectionRunnerManifestSHA256
      ≡
      "3d0ba75bb95899fa59f0bc28043f27653db36ca56acf28deaebf916435716a09"

    noPosteriorTuningAttestationPath :
      String

    noPosteriorTuningAttestationSHA256 :
      String

    noPosteriorTuningAttestationSHA256IsCanonical :
      noPosteriorTuningAttestationSHA256
      ≡
      "596d72909c6d6fb5659b455f21af199c2ca39243edd9b9e2f2e963730961741c"

    repoLocalVenvPython :
      String

    repoLocalVenvPythonIsCanonical :
      repoLocalVenvPython
      ≡
      "/home/c/Documents/code/dashi_agda/.venv/bin/python"

    runtimeAuthoritiesPopulated :
      Bool

    runtimeAuthoritiesPopulatedIsTrue :
      runtimeAuthoritiesPopulated ≡ true

open PenguinRuntimeAuthorityArtifactReceipt public

canonicalPenguinRuntimeAuthorityArtifactReceipt :
  PenguinRuntimeAuthorityArtifactReceipt
canonicalPenguinRuntimeAuthorityArtifactReceipt =
  mkPenguinRuntimeAuthorityArtifactReceipt
    "scripts/data/hepdata/penguin_gate5_sm_baseline_flavio_2_7_0.json"
    "469aaab75326d6f39678783d8b32b6be22a6b299c43043865eb1679d259dd476"
    refl
    "scripts/data/hepdata/penguin_gate5_sm_prediction_flavio_2_7_0_runtime_snapshot.json"
    "fa690ebff9fa508cf553671e5d8f5fb98e3718c4643fabfb0459dc56a0e8ccda"
    refl
    "BR(Bs->mumu)"
    refl
    "3.6289314570849374e-09"
    refl
    "scripts/data/hepdata/penguin_gate5_wilson_authority_manifest.json"
    "f443742a9207a8b1493b84934e21a7c980839434c49257e0bb649077aafd4585"
    refl
    "2.5.2"
    refl
    "959e3dbd6bfefb43b3769fe07e2d8e59c153abe6796851fb91c4d18b7981799a"
    refl
    "flavio-2.7.0-wheel-sha256:3d5aaeb5a9df7c479949e4641ccbd2dc662cb010aabf9dda5f725a8a80813b4f"
    refl
    "scripts/data/hepdata/penguin_gate5_projection_runner_manifest.json"
    "3d0ba75bb95899fa59f0bc28043f27653db36ca56acf28deaebf916435716a09"
    refl
    "scripts/data/hepdata/penguin_gate5_no_posterior_tuning_attestation.txt"
    "596d72909c6d6fb5659b455f21af199c2ca39243edd9b9e2f2e963730961741c"
    refl
    "/home/c/Documents/code/dashi_agda/.venv/bin/python"
    refl
    true
    refl

record PenguinFreezeHashFormulaSurface : Set where
  constructor mkPenguinFreezeHashFormulaSurface
  field
    formulaName :
      String

    digestAlgorithm :
      String

    digestAlgorithmIsSHA256 :
      digestAlgorithm ≡ "sha256"

    canonicalPreimageEncoding :
      String

    canonicalFieldOrder :
      List String

    formulaText :
      String

    currentDiagnosticHEAD :
      String

    worktreeCleanAtFreezePoint :
      Bool

    worktreeCleanAtFreezePointIsFalse :
      worktreeCleanAtFreezePoint ≡ false

    acceptedFreezeHashPopulated :
      Bool

    acceptedFreezeHashPopulatedIsFalse :
      acceptedFreezeHashPopulated ≡ false

    populatedFreezeHash :
      String

    populatedFreezeHashIsGap :
      populatedFreezeHash
      ≡
      "gap: accepted freeze hash requires clean worktree plus complete canonical preimage"

open PenguinFreezeHashFormulaSurface public

canonicalPenguinFreezeHashFormulaSurface :
  PenguinFreezeHashFormulaSurface
canonicalPenguinFreezeHashFormulaSurface =
  mkPenguinFreezeHashFormulaSurface
    "penguin-freeze-hash-v1"
    "sha256"
    refl
    "UTF-8 LF-delimited key=value lines, exact field order, no trailing spaces, final LF"
    ( "selected_dataset_artifact"
      ∷ "hepdata_record_or_table_identifier"
      ∷ "hepdata_value_table_sha256"
      ∷ "hepdata_covariance_table_sha256"
      ∷ "flavio_version"
      ∷ "flavio_wheel_sha256"
      ∷ "flavio_sdist_sha256"
      ∷ "sm_baseline_artifact_sha256"
      ∷ "wilson_authority_artifact_sha256"
      ∷ "ckm_source_commit_or_revision"
      ∷ "projection_code_clean_git_head"
      ∷ "projection_runner_artifact_sha256"
      ∷ "no_posterior_tuning_attestation"
      ∷ [] )
    "freeze_hash = sha256(canonical UTF-8 LF-delimited preimage over the listed field order)"
    "81fc16c11af4f4152410ea9ce9269c68cc223387"
    false
    refl
    false
    refl
    "gap: accepted freeze hash requires clean worktree plus complete canonical preimage"
    refl

record PenguinExternalAuthorityFreezeInjectionReceipt : Setω where
  field
    status :
      PenguinExternalAuthorityInjectionStatus

    hepdataIns2000945 :
      HEPDataPenguinLookupReceipt

    hepdataIns1394303 :
      HEPDataPenguinLookupReceipt

    cmsHEPDataRecordMetadata :
      CMSHEPDataRecordMetadataReceipt

    flavioPyPIArtifactHashes :
      FlavioPyPIArtifactHashReceipt

    runtimeAuthorityArtifacts :
      PenguinRuntimeAuthorityArtifactReceipt

    freezeHashFormulaSurface :
      PenguinFreezeHashFormulaSurface

    cmsRecordMetadataChecksumPopulated :
      Bool

    cmsRecordMetadataChecksumPopulatedIsTrue :
      cmsRecordMetadataChecksumPopulated ≡ true

    cmsProfileLikelihoodTableResolved :
      Bool

    cmsProfileLikelihoodTableResolvedIsTrue :
      cmsProfileLikelihoodTableResolved ≡ true

    cmsProfileLikelihoodTablePayloadSHA256Populated :
      Bool

    cmsProfileLikelihoodTablePayloadSHA256PopulatedIsTrue :
      cmsProfileLikelihoodTablePayloadSHA256Populated ≡ true

    anyHEPDataTableSHA256Populated :
      Bool

    anyHEPDataTableSHA256PopulatedIsTrue :
      anyHEPDataTableSHA256Populated ≡ true

    flavioHashesPopulated :
      Bool

    flavioHashesPopulatedIsTrue :
      flavioHashesPopulated ≡ true

    smBaselineArtifactSHA256Populated :
      Bool

    smBaselineArtifactSHA256PopulatedIsTrue :
      smBaselineArtifactSHA256Populated ≡ true

    wilsonAuthorityArtifactSHA256Populated :
      Bool

    wilsonAuthorityArtifactSHA256PopulatedIsTrue :
      wilsonAuthorityArtifactSHA256Populated ≡ true

    ckmSourceCommitOrRevisionPopulated :
      Bool

    ckmSourceCommitOrRevisionPopulatedIsTrue :
      ckmSourceCommitOrRevisionPopulated ≡ true

    projectionRunnerArtifactSHA256Populated :
      Bool

    projectionRunnerArtifactSHA256PopulatedIsTrue :
      projectionRunnerArtifactSHA256Populated ≡ true

    noPosteriorTuningAttestationPopulated :
      Bool

    noPosteriorTuningAttestationPopulatedIsTrue :
      noPosteriorTuningAttestationPopulated ≡ true

    projectionCodeCleanGitHeadPopulated :
      Bool

    projectionCodeCleanGitHeadPopulatedIsFalse :
      projectionCodeCleanGitHeadPopulated ≡ false

    acceptedFreezeHashPopulated :
      Bool

    acceptedFreezeHashPopulatedIsFalse :
      acceptedFreezeHashPopulated ≡ false

    acceptedExternalAuthorityTokenConstructed :
      Bool

    acceptedExternalAuthorityTokenConstructedIsFalse :
      acceptedExternalAuthorityTokenConstructed ≡ false

    boundaries :
      List PenguinExternalAuthorityBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalPenguinExternalAuthorityBoundaries

    acceptedAuthorityTokenImpossible :
      AcceptedPenguinExternalAuthorityToken →
      ⊥

open PenguinExternalAuthorityFreezeInjectionReceipt public

canonicalPenguinExternalAuthorityFreezeInjectionReceipt :
  PenguinExternalAuthorityFreezeInjectionReceipt
canonicalPenguinExternalAuthorityFreezeInjectionReceipt =
  record
    { status =
        datasetSMWilsonAttestationPopulatedCleanCodeHeadStillGap
    ; hepdataIns2000945 =
        hepdataIns2000945LookupReceipt
    ; hepdataIns1394303 =
        hepdataIns1394303LookupReceipt
    ; cmsHEPDataRecordMetadata =
        canonicalCMSHEPDataRecordMetadataReceipt
    ; flavioPyPIArtifactHashes =
        canonicalFlavioPyPIArtifactHashReceipt
    ; runtimeAuthorityArtifacts =
        canonicalPenguinRuntimeAuthorityArtifactReceipt
    ; freezeHashFormulaSurface =
        canonicalPenguinFreezeHashFormulaSurface
    ; cmsRecordMetadataChecksumPopulated =
        true
    ; cmsRecordMetadataChecksumPopulatedIsTrue =
        refl
    ; cmsProfileLikelihoodTableResolved =
        true
    ; cmsProfileLikelihoodTableResolvedIsTrue =
        refl
    ; cmsProfileLikelihoodTablePayloadSHA256Populated =
        true
    ; cmsProfileLikelihoodTablePayloadSHA256PopulatedIsTrue =
        refl
    ; anyHEPDataTableSHA256Populated =
        true
    ; anyHEPDataTableSHA256PopulatedIsTrue =
        refl
    ; flavioHashesPopulated =
        true
    ; flavioHashesPopulatedIsTrue =
        refl
    ; smBaselineArtifactSHA256Populated =
        true
    ; smBaselineArtifactSHA256PopulatedIsTrue =
        refl
    ; wilsonAuthorityArtifactSHA256Populated =
        true
    ; wilsonAuthorityArtifactSHA256PopulatedIsTrue =
        refl
    ; ckmSourceCommitOrRevisionPopulated =
        true
    ; ckmSourceCommitOrRevisionPopulatedIsTrue =
        refl
    ; projectionRunnerArtifactSHA256Populated =
        true
    ; projectionRunnerArtifactSHA256PopulatedIsTrue =
        refl
    ; noPosteriorTuningAttestationPopulated =
        true
    ; noPosteriorTuningAttestationPopulatedIsTrue =
        refl
    ; projectionCodeCleanGitHeadPopulated =
        false
    ; projectionCodeCleanGitHeadPopulatedIsFalse =
        refl
    ; acceptedFreezeHashPopulated =
        false
    ; acceptedFreezeHashPopulatedIsFalse =
        refl
    ; acceptedExternalAuthorityTokenConstructed =
        false
    ; acceptedExternalAuthorityTokenConstructedIsFalse =
        refl
    ; boundaries =
        canonicalPenguinExternalAuthorityBoundaries
    ; boundariesAreCanonical =
        refl
    ; acceptedAuthorityTokenImpossible =
        acceptedPenguinExternalAuthorityTokenImpossibleHere
    }

canonicalPenguinExternalAuthorityCMSHEPDataSHAPopulated :
  anyHEPDataTableSHA256Populated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthorityCMSHEPDataSHAPopulated =
  refl

canonicalPenguinExternalAuthorityCMSMetadataPopulated :
  cmsRecordMetadataChecksumPopulated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthorityCMSMetadataPopulated =
  refl

canonicalPenguinExternalAuthorityCMSProfileLikelihoodResolved :
  cmsProfileLikelihoodTableResolved
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthorityCMSProfileLikelihoodResolved =
  refl

canonicalPenguinExternalAuthorityCMSProfilePayloadPopulated :
  cmsProfileLikelihoodTablePayloadSHA256Populated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthorityCMSProfilePayloadPopulated =
  refl

canonicalPenguinExternalAuthorityFlavioHashesPopulated :
  flavioHashesPopulated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthorityFlavioHashesPopulated =
  refl

canonicalPenguinExternalAuthoritySMBaselinePopulated :
  smBaselineArtifactSHA256Populated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthoritySMBaselinePopulated =
  refl

canonicalPenguinExternalAuthorityWilsonPopulated :
  wilsonAuthorityArtifactSHA256Populated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthorityWilsonPopulated =
  refl

canonicalPenguinExternalAuthorityNoPosteriorTuningPopulated :
  noPosteriorTuningAttestationPopulated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  true
canonicalPenguinExternalAuthorityNoPosteriorTuningPopulated =
  refl

canonicalPenguinExternalAuthorityCleanHeadStillGap :
  projectionCodeCleanGitHeadPopulated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  false
canonicalPenguinExternalAuthorityCleanHeadStillGap =
  refl

canonicalPenguinExternalAuthorityFreezeHashStillGap :
  acceptedFreezeHashPopulated
    canonicalPenguinExternalAuthorityFreezeInjectionReceipt
  ≡
  false
canonicalPenguinExternalAuthorityFreezeHashStillGap =
  refl
